/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.Bertrand

/-!
# Continuous Turán numbers in finite dimensions

Translating a planar pattern preserves its continuous Turán number, and enlarging the square
can only increase it. For a single point, both the saturation function and the continuous Turán
number vanish.
The volume gained by enlarging the ambient cube bounds the increase in the supremum of volumes
of open sets avoiding a fixed pattern.

Two or three copies of a plus sign stacked along the third axis have continuous Turán numbers of
order $n^{5/2}$ and $n^{8/3}$ in $[0, n]^3$. The upper bounds count pairs (or triples) of heights
whose slices share a point with room for both arms of the plus sign, as in the
Kővári–Sós–Turán theorem. The lower bounds put boxes on the incidences of points and lines of
$\mathbb{F}_p^2$, and on a unit-sphere graph of $\mathbb{F}_p^3$ in the style of Brown's
construction, which has no $K_{3,3}$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Containment of planar point sets.** A set $S \subseteq \mathbb{R}^2$ contains a set
$P \subseteq \mathbb{R}^2$ when there are maps $f_X, f_Y : \mathbb{R} \to \mathbb{R}$ such that
$f_X(x_0) - f_X(x_1) \ge x_0 - x_1$ whenever $x_0 > x_1$ are $x$-coordinates of points of $P$,
$f_Y(y_0) - f_Y(y_1) \ge y_0 - y_1$ whenever $y_0 > y_1$ are $y$-coordinates of points of $P$,
and $(f_X(x), f_Y(y)) \in S$ for every $(x, y) \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public def PointSetContainsPattern (S P : Set (ℝ × ℝ)) : Prop :=
  ∃ fX fY : ℝ → ℝ,
    (∀ p ∈ P, ∀ q ∈ P, q.1 < p.1 → p.1 - q.1 ≤ fX p.1 - fX q.1) ∧
    (∀ p ∈ P, ∀ q ∈ P, q.2 < p.2 → p.2 - q.2 ≤ fY p.2 - fY q.2) ∧
    ∀ p ∈ P, (fX p.1, fY p.2) ∈ S

/-- **Every planar set contains the empty pattern.** Every set $S \subseteq \mathbb{R}^2$ contains
the empty set $\emptyset$ in the sense of containment of planar point sets.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of containment). -/
public theorem pointSetContainsPattern_empty (S : Set (ℝ × ℝ)) : PointSetContainsPattern S ∅ :=
  ⟨id, id, by simp, by simp, by simp⟩

/-- **Continuous Turán number in the plane.** For a real number $n$ and a set
$P \subseteq \mathbb{R}^2$, the continuous Turán number $\operatorname{opx}(n, P)$ is the supremum
of the Lebesgue measures $\mu_2(S)$ over all open sets $S \subseteq [0, n]^2$ that do not contain
$P$ in the sense of point-set pattern containment; it is $0$ when there is no such set.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public noncomputable def opx (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P})

/-- **Nonnegativity of the continuous Turán number.** For every real number $n$ and every set
$P \subseteq \mathbb{R}^2$, $\operatorname{opx}(n, P) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ opx n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- **Continuous Turán number of the empty pattern.** For every real number $n$,
$\mathrm{opx}(n, \emptyset) = 0$: every set contains the empty pattern, so no set avoids it.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1
(definition of `opx(n, P)`). -/
public theorem opx_empty (n : ℝ) : opx n ∅ = 0 := by
  simp [opx, pointSetContainsPattern_empty]

private theorem opx_translate.contains_translate {S P : Set (ℝ × ℝ)}
    (h : PointSetContainsPattern S P) (v : ℝ × ℝ) :
    PointSetContainsPattern S ((fun p => p + v) '' P) := by
  obtain ⟨f, g, hf, hg, hmem⟩ := h
  refine ⟨fun x => f (x - v.1), fun y => g (y - v.2), ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hlt
    simpa using hf p hp q hq (by simpa using hlt)
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hlt
    simpa using hg p hp q hq (by simpa using hlt)
  · rintro _ ⟨p, hp, rfl⟩
    simpa using hmem p hp

/-- **Translation invariance of the continuous Turán number.** Let $n$ be a real number,
$P \subseteq \mathbb{R}^2$ a set and $v \in \mathbb{R}^2$ a vector, and let
$P + v = \{p + v : p \in P\}$ be the translate of $P$ by $v$. Then
$\operatorname{opx}(n, P + v) = \operatorname{opx}(n, P)$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.2
(`integers-2024-A1-lem-2-2`). -/
public theorem opx_translate (n : ℝ) (P : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    opx n ((fun p => p + v) '' P) = opx n P := by
  have h (S : Set (ℝ × ℝ)) :
      PointSetContainsPattern S ((fun p => p + v) '' P) ↔ PointSetContainsPattern S P := by
    refine ⟨fun ht => ?_, fun hp => opx_translate.contains_translate hp v⟩
    simpa only [Set.image_image, add_assoc, add_neg_cancel, add_zero, Set.image_id'] using
      opx_translate.contains_translate ht (-v)
  simp only [opx, h]

open Set MeasureTheory in
/-- **Monotonicity of the continuous Turán number in the side length.** For every set
$P \subseteq \mathbb{R}^2$ and all real numbers $m \le n$, the continuous Turán numbers satisfy
$\operatorname{opx}(m, P) \le \operatorname{opx}(n, P)$.

The paper assumes $0 < m$. This is not needed, since $\operatorname{opx}(m, P) = 0$ for $m \le 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 2.4
(`integers-2024-A1-lem-2-4`). -/
public theorem opx_mono_left (P : Set (ℝ × ℝ)) {m n : ℝ} (hmn : m ≤ n) :
    opx m P ≤ opx n P := by
  have hI : Icc 0 m ⊆ Icc 0 n := Icc_subset_Icc_right hmn
  apply Real.sSup_le _ (opx_nonneg n P)
  rintro _ ⟨S, ⟨hopen, hSm, hfree⟩, rfl⟩
  refine le_csSup ?_ ⟨S, ⟨hopen, hSm.trans (prod_mono hI hI), hfree⟩, rfl⟩
  refine ⟨volume.real (Icc 0 n ×ˢ Icc 0 n), ?_⟩
  rintro _ ⟨T, ⟨_, hTn, _⟩, rfl⟩
  exact measureReal_mono hTn (isCompact_Icc.prod isCompact_Icc).measure_ne_top

/-- **Saturating sets for a point pattern.** Let $n$ be a real number and let $P$ and $S$ be
subsets of $\mathbb{R}^2$. Then $S$ is saturating for $P$ in $[0, n]^2$ when $S$ is an open
subset of $[0, n]^2$ that does not contain $P$, while every open set $S'$ with
$S \subsetneq S' \subseteq [0, n]^2$ contains $P$. Here a set $T$ contains $P$ when there are
maps $f_X, f_Y : \mathbb{R} \to \mathbb{R}$ such that $f_X(x) - f_X(x') \ge x - x'$ whenever
$x > x'$ are $x$-coordinates of points of $P$, likewise $f_Y(y) - f_Y(y') \ge y - y'$ whenever
$y > y'$ are $y$-coordinates of points of $P$, and $(f_X(x), f_Y(y)) \in T$ for every
$(x, y) \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of saturating sets). -/
public def IsOpxSaturating (n : ℝ) (P S : Set (ℝ × ℝ)) : Prop :=
  IsOpen S ∧ S ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n ∧ ¬ PointSetContainsPattern S P ∧
    ∀ S' : Set (ℝ × ℝ), IsOpen S' → S' ⊆ Set.Icc 0 n ×ˢ Set.Icc 0 n → S ⊂ S' →
      PointSetContainsPattern S' P

/-- **Saturation function for continuous patterns.** For a real number $n$ and a set
$P \subseteq \mathbb{R}^2$, call an open set $S \subseteq [0, n]^2$ saturating for $P$ if $S$
does not contain $P$ but every open set $S' \subseteq [0, n]^2$ properly containing $S$ contains
$P$ (containment in the sense of point-set pattern containment). The saturation function
$\operatorname{osat}(n, P)$ is the infimum of the Lebesgue measures $\mu_2(S)$ over all sets $S$
saturating for $P$, and is $0$ when no saturating set exists.

The paper leaves $\operatorname{osat}(n, P)$ undefined when no saturating set exists.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public noncomputable def osat (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sInf ((fun S => (MeasureTheory.volume S).toReal) '' {S | IsOpxSaturating n P S})

/-- **The saturation function is nonnegative.** For every real number $n$ and every set
$P \subseteq \mathbb{R}^2$, $\operatorname{osat}(n, P) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6
(definition of `osat(n, P)`). -/
public theorem osat_nonneg (n : ℝ) (P : Set (ℝ × ℝ)) : 0 ≤ osat n P := by
  apply Real.sInf_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

open Set in
/-- **Saturation function and continuous Turán number of a single point.** For every real number
$n$ and every point $p \in \mathbb{R}^2$, $\operatorname{osat}(n, \{p\}) = 0$ and
$\operatorname{opx}(n, \{p\}) = 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 6.5
(`integers-2024-A1-lem-6-5`). -/
public theorem osat_singleton_and_opx_singleton (n : ℝ) (p : ℝ × ℝ) :
    osat n {p} = 0 ∧ opx n {p} = 0 := by
  have contains (S : Set (ℝ × ℝ)) : PointSetContainsPattern S {p} ↔ S.Nonempty := by
    constructor
    · rintro ⟨f, g, _, _, h⟩
      exact ⟨_, h p (mem_singleton p)⟩
    · rintro ⟨q, hq⟩
      exact ⟨fun _ => q.1, fun _ => q.2, by simp, by simp, by simpa using hq⟩
  have free (S : Set (ℝ × ℝ)) :
      (IsOpen S ∧ S ⊆ Icc 0 n ×ˢ Icc 0 n ∧ ¬ PointSetContainsPattern S {p}) ↔ S = ∅ := by
    rw [contains, not_nonempty_iff_eq_empty]
    exact ⟨fun h => h.2.2, by rintro rfl; simp⟩
  have saturating (S : Set (ℝ × ℝ)) : IsOpxSaturating n {p} S ↔ S = ∅ := by
    constructor
    · exact fun h => (free S).1 ⟨h.1, h.2.1, h.2.2.1⟩
    · rintro rfl
      refine ⟨isOpen_empty, empty_subset _, ?_, fun T _ _ hT => (contains T).2 ?_⟩
      · simp [contains]
      · exact empty_ssubset.mp hT
  simp only [osat, opx, saturating, free]
  simp

/-- **Containment of point sets in $\mathbb{R}^d$.** Let $d$ be a natural number and let
$S, P \subseteq \mathbb{R}^d$. Then $S$ contains $P$ when there are maps
$f_1, \dots, f_d : \mathbb{R} \to \mathbb{R}$ that expand distances between coordinates of points
of $P$, that is, $f_i(p_i) - f_i(q_i) \ge p_i - q_i$ for every $i$ and all $p, q \in P$ with
$p_i > q_i$, and such that $(f_1(p_1), \dots, f_d(p_d)) \in S$ for every $p \in P$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public def ContainsPatternD {d : ℕ} (S P : Set (Fin d → ℝ)) : Prop :=
  ∃ f : Fin d → ℝ → ℝ,
    (∀ i, ∀ p ∈ P, ∀ q ∈ P, q i < p i → p i - q i ≤ f i (p i) - f i (q i)) ∧
    ∀ p ∈ P, (fun i => f i (p i)) ∈ S

/-- **Every set in $\mathbb{R}^d$ contains the empty pattern.** For every natural number $d$ and
every set $S \subseteq \mathbb{R}^d$, $S$ contains the empty set $\emptyset \subseteq \mathbb{R}^d$
in the sense of containment of point sets in $\mathbb{R}^d$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of containment in `ℝ^d`). -/
public theorem containsPatternD_empty {d : ℕ} (S : Set (Fin d → ℝ)) : ContainsPatternD S ∅ :=
  ⟨fun _ => id, by simp, by simp⟩

/-- **Continuous Turán number in $\mathbb{R}^d$.** For a natural number $d$, a real number $n$
and a set $P \subseteq \mathbb{R}^d$, the continuous Turán number $\mathrm{opx}(n, P, d)$ is the
supremum of the $d$-dimensional Lebesgue measures $\mu_d(S)$ over all open sets
$S \subseteq [0, n]^d$ that do not contain $P$ in the sense of containment of point sets in
$\mathbb{R}^d$; it is $0$ when there is no such set.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public noncomputable def opxD (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : ℝ :=
  sSup ((fun S => (MeasureTheory.volume S).toReal) ''
    {S | IsOpen S ∧ S ⊆ Set.Icc 0 (fun _ => n) ∧ ¬ ContainsPatternD S P})

/-- **Higher-dimensional continuous Turán numbers are nonnegative.** For every dimension $d$,
real number $n$ and set $P \subseteq \mathbb{R}^d$, $\mathrm{opx}(n, P, d) \ge 0$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_nonneg (d : ℕ) (n : ℝ) (P : Set (Fin d → ℝ)) : 0 ≤ opxD d n P := by
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  exact ENNReal.toReal_nonneg

/-- **The higher-dimensional continuous Turán number of the empty pattern.** For every dimension
$d$ and every real number $n$, $\mathrm{opx}(n, \emptyset, d) = 0$: every set contains the empty
pattern, so no set is free of it.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 5
(definition of `opx(n, P, d)`). -/
public theorem opxD_empty (d : ℕ) (n : ℝ) : opxD d n ∅ = 0 := by
  simp [opxD, containsPatternD_empty]

open Set MeasureTheory

private theorem opxD_add_lt.volume_le_opxD {d : ℕ} {n : ℝ} {S P : Set (Fin d → ℝ)}
    (hS : IsOpen S) (hSn : S ⊆ Icc 0 (fun _ => n)) (hP : ¬ ContainsPatternD S P) :
    volume.real S ≤ opxD d n P := by
  unfold opxD
  refine le_csSup ?_ ⟨S, ⟨hS, hSn, hP⟩, rfl⟩
  refine ⟨volume.real (Icc (0 : Fin d → ℝ) (fun _ => n)), ?_⟩
  rintro _ ⟨T, ⟨_, hT, _⟩, rfl⟩
  exact measureReal_mono hT isCompact_Icc.measure_ne_top

/-- **Higher-dimensional continuous Turán numbers are monotone under containment.** Let
$P, Q \subseteq \mathbb{R}^d$. If $Q$ contains $P$, then
$\mathrm{opx}(n, P, d) \le \mathrm{opx}(n, Q, d)$ for every real number $n$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.1
(`integers-2024-A1-lem-5-1`). -/
public theorem opxD_mono_of_containsPatternD {d : ℕ} (n : ℝ) {P Q : Set (Fin d → ℝ)}
    (h : ContainsPatternD Q P) : opxD d n P ≤ opxD d n Q := by
  apply Real.sSup_le _ (opxD_nonneg ..)
  rintro _ ⟨S, ⟨hS, hSn, hfree⟩, rfl⟩
  apply opxD_add_lt.volume_le_opxD hS hSn
  rintro ⟨g, hg, hgS⟩
  obtain ⟨f, hf, hfQ⟩ := h
  apply hfree
  refine ⟨fun i => g i ∘ f i, ?_, fun p hp => hgS _ (hfQ p hp)⟩
  intro i p hp q hq hlt
  have hgap := hf i p hp q hq hlt
  have hlt' := sub_pos.mp ((sub_pos.mpr hlt).trans_le hgap)
  exact hgap.trans (hg i _ (hfQ p hp) _ (hfQ q hq) hlt')

/-- **Increment bound for the d-dimensional continuous Turán number.** Let $d \ge 2$ be a
natural number, let $P \subseteq \mathbb{R}^d$, and let $n, \varepsilon$ be real numbers with
$n > 0$ and $0 < \varepsilon < n$. Then the $d$-dimensional continuous Turán number
$\mathrm{opx}$ satisfies $\mathrm{opx}(n, P, d) \le \mathrm{opx}(n + \varepsilon, P, d)$ and
$\mathrm{opx}(n + \varepsilon, P, d) < \mathrm{opx}(n, P, d) + d (2n)^{d-1} \varepsilon$.

The hypothesis $d \ge 2$ is needed: for $d = 1$ and $P = \{0, L\}$ with $L > n + \varepsilon$,
every open subset of $[0, n + \varepsilon]$ avoids $P$, so
$\mathrm{opx}(n + \varepsilon, P, 1) = n + \varepsilon = \mathrm{opx}(n, P, 1) + \varepsilon$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.3
(`integers-2024-A1-lem-5-3`). -/
public theorem opxD_add_lt {d : ℕ} (hd : 2 ≤ d) (P : Set (Fin d → ℝ)) {n ε : ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hεn : ε < n) :
    opxD d n P ≤ opxD d (n + ε) P ∧
      opxD d (n + ε) P < opxD d n P + d * (2 * n) ^ (d - 1) * ε := by
  have hnm : n ≤ n + ε := le_add_of_nonneg_right hε.le
  have hboxes : Icc (0 : Fin d → ℝ) (fun _ => n) ⊆ Icc 0 (fun _ => n + ε) :=
    Icc_subset_Icc_right (fun _ => hnm)
  constructor
  · apply Real.sSup_le _ (opxD_nonneg ..)
    rintro _ ⟨S, ⟨hS, hSn, hP⟩, rfl⟩
    exact opxD_add_lt.volume_le_opxD hS (hSn.trans hboxes) hP
  -- Cutting an open competitor down to the open inner cube preserves pattern avoidance.
  -- The discarded part lies in the shell between the two cubes.
  let U := univ.pi fun _ : Fin d => Ioo 0 n
  let B := Icc (0 : Fin d → ℝ) (fun _ => n + ε)
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hUn : U ⊆ Icc (0 : Fin d → ℝ) (fun _ => n) := fun x hx =>
    ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩
  have hB : volume B ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hUV : volume.real U = n ^ d := by
    simpa [U, Measure.real] using
      (Real.volume_pi_Ioo_toReal (a := fun _ : Fin d => 0) (b := fun _ => n) (fun _ => hn.le))
  have hBV : volume.real B = (n + ε) ^ d := by
    simpa [B, Measure.real] using
      (Real.volume_Icc_pi_toReal (a := (0 : Fin d → ℝ)) (b := fun _ => n + ε)
        (fun _ => hn.le.trans hnm))
  have hshell : volume.real (B \ U) = (n + ε) ^ d - n ^ d := by
    rw [measureReal_sdiff (hUn.trans hboxes) hU.measurableSet hB, hUV, hBV]
  have hbound : opxD d (n + ε) P ≤ opxD d n P + volume.real (B \ U) := by
    apply Real.sSup_le _ (add_nonneg (opxD_nonneg ..) measureReal_nonneg)
    rintro _ ⟨S, ⟨hS, hSB, hP⟩, rfl⟩
    have hinner : volume.real (S ∩ U) ≤ opxD d n P := by
      apply opxD_add_lt.volume_le_opxD (hS.inter hU) (inter_subset_right.trans hUn)
      rintro ⟨f, hf, himg⟩
      exact hP ⟨f, hf, fun p hp => (himg p hp).1⟩
    have houter : volume.real (S \ U) ≤ volume.real (B \ U) :=
      measureReal_mono (sdiff_subset_sdiff_left hSB) (measure_ne_top_of_subset sdiff_subset hB)
    exact (measureReal_inter_add_sdiff hU.measurableSet (measure_ne_top_of_subset hSB hB)).ge.trans
      (add_le_add hinner houter)
  rw [hshell] at hbound
  apply hbound.trans_lt (add_lt_add_right ?_ _)
  have hpow := (le_abs_self _).trans (abs_pow_sub_pow_le (n + ε) n d)
  rw [add_sub_cancel_left, abs_of_pos hε, abs_of_pos (add_pos hn hε), abs_of_pos hn,
    max_eq_left hnm] at hpow
  calc
    _ ≤ ε * d * (n + ε) ^ (d - 1) := hpow
    _ < ε * d * (2 * n) ^ (d - 1) := by
      apply mul_lt_mul_of_pos_left _ (mul_pos hε (Nat.cast_pos.mpr (by omega)))
      exact pow_lt_pow_left₀ (by linarith) (hn.le.trans hnm) (by omega)
    _ = _ := by ring

open scoped ENNReal NNReal

namespace opxD_plus_stack_isTheta

/-- The coordinate map `((x, y), z) ↦ (x, y, z)` preserves Lebesgue measure. -/
private theorem measurePreserving_vec3 :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) volume volume := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  refine ⟨hm, ?_⟩
  rw [volume_pi]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun q : (ℝ × ℝ) × ℝ => ![q.1.1, q.1.2, q.2]) ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ s 2 := by
    ext q
    simp [Fin.forall_fin_succ, and_assoc]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Fin.prod_univ_three]


/-- The points of a set `H ⊆ ℝ` that have at most `R` of `H` to their right form a set of
measure at most `R`. -/
private theorem volume_room_right_le {H : Set ℝ} (hH : BddBelow H) (R : ℝ≥0∞) :
    volume {a | a ∈ H ∧ volume (H ∩ Ioi a) ≤ R} ≤ R := by
  set E := {a | a ∈ H ∧ volume (H ∩ Ioi a) ≤ R}
  rcases E.eq_empty_or_nonempty with hE | hE
  · simp [hE]
  have hEb : BddBelow E := hH.mono fun a ha => ha.1
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨a, haE, has⟩ :=
    exists_lt_of_csInf_lt hE (lt_add_of_pos_right (sInf E) (NNReal.coe_pos.2 hε))
  calc volume E ≤ volume (Ico (sInf E) a ∪ (H ∩ Ioi a ∪ {a})) := by
        refine measure_mono fun x hx => ?_
        rcases lt_trichotomy x a with hxa | rfl | hxa
        · exact Or.inl ⟨csInf_le hEb hx, hxa⟩
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl ⟨hx.1, hxa⟩)
    _ ≤ volume (Ico (sInf E) a) + (volume (H ∩ Ioi a) + volume ({a} : Set ℝ)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ε + (R + 0) := by
        gcongr
        · rw [Real.volume_Ico, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · exact haE.2
        · simp
    _ = R + ε := by rw [add_zero, add_comm]

/-- The points of a set `H ⊆ ℝ` that have at most `R` of `H` to their left form a set of
measure at most `R`. -/
private theorem volume_room_left_le {H : Set ℝ} (hH : BddAbove H) (R : ℝ≥0∞) :
    volume {a | a ∈ H ∧ volume (H ∩ Iio a) ≤ R} ≤ R := by
  set E := {a | a ∈ H ∧ volume (H ∩ Iio a) ≤ R}
  rcases E.eq_empty_or_nonempty with hE | hE
  · simp [hE]
  have hEb : BddAbove E := hH.mono fun a ha => ha.1
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨a, haE, has⟩ :=
    exists_lt_of_lt_csSup hE (sub_lt_self (sSup E) (NNReal.coe_pos.2 hε))
  calc volume E ≤ volume (Ioc a (sSup E) ∪ (H ∩ Iio a ∪ {a})) := by
        refine measure_mono fun x hx => ?_
        rcases lt_trichotomy x a with hxa | rfl | hxa
        · exact Or.inr (Or.inl ⟨hx.1, hxa⟩)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨hxa, le_csSup hEb hx⟩
    _ ≤ volume (Ioc a (sSup E)) + (volume (H ∩ Iio a) + volume ({a} : Set ℝ)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ε + (R + 0) := by
        gcongr
        · rw [Real.volume_Ioc, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · exact haE.2
        · simp
    _ = R + ε := by rw [add_zero, add_comm]

/-- A compact set `K ⊆ (a, ∞)` of measure at least `r` receives a map `g` with `g 0 = a` that
expands distances on `[0, r]` and sends `(0, r]` into `K`. -/
private theorem exists_arm_right {K : Set ℝ} (hK : IsCompact K) {a r : ℝ}
    (hKa : K ⊆ Ioi a) (hKr : ENNReal.ofReal r ≤ volume K) :
    ∃ g : ℝ → ℝ, g 0 = a ∧ (∀ x ∈ Ioc 0 r, g x ∈ K) ∧
      ∀ x ∈ Icc 0 r, ∀ x' ∈ Icc 0 r, x' < x → x - x' ≤ g x - g x' := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · have hr : r ≤ 0 := by simpa using hKr
    refine ⟨fun _ => a, rfl, fun x hx => absurd hx.2 (by linarith [hx.1]), ?_⟩
    intro x hx x' hx' hlt
    linarith [hx.2, hx'.1]
  set F : ℝ → ℝ := fun s => (volume (K ∩ Iic s)).toReal with hF
  have hKfin : volume K ≠ ∞ := hK.measure_ne_top
  have hfin : ∀ s, volume (K ∩ Iic s) ≠ ∞ := fun s =>
    measure_ne_top_of_subset inter_subset_left hKfin
  have hFle : ∀ s' s, s' ≤ s → F s ≤ F s' + (s - s') := by
    intro s' s hss
    have h1 : K ∩ Iic s ⊆ (K ∩ Iic s') ∪ Ioc s' s := fun y hy => by
      by_cases hy' : y ≤ s'
      · exact Or.inl ⟨hy.1, hy'⟩
      · exact Or.inr ⟨not_le.1 hy', hy.2⟩
    have h2 := (measure_mono (μ := volume) h1).trans (measure_union_le _ _)
    rw [Real.volume_Ioc] at h2
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin s', ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add (hfin s') ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h3
  have hFmono : Monotone F := fun s' s hss =>
    ENNReal.toReal_mono (hfin s)
      (measure_mono (μ := volume) (inter_subset_inter_right _ (Iic_subset_Iic.2 hss)))
  have hFcont : Continuous F := by
    refine (LipschitzWith.of_le_add fun s s' => ?_).continuous
    rcases le_total s' s with h | h
    · have := hFle s' s h
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    · have := hFmono h
      linarith [dist_nonneg (x := s) (y := s')]
  classical
  let A : ℝ → Set ℝ := fun x => K ∩ F ⁻¹' Ici x
  let g : ℝ → ℝ := fun x => if 0 < x then sInf (A x) else a
  have hsup : sSup K ∈ K := hK.sSup_mem hne
  have hFsup : r ≤ F (sSup K) := by
    have : K ∩ Iic (sSup K) = K := inter_eq_left.2 fun y hy => le_csSup hK.bddAbove hy
    simp only [F, this]
    exact (ENNReal.ofReal_le_iff_le_toReal hKfin).1 hKr
  have hAne : ∀ x ≤ r, (A x).Nonempty := fun x hx => ⟨sSup K, hsup, hx.trans hFsup⟩
  have hAcl : ∀ x, IsClosed (A x) := fun x => hK.isClosed.inter (isClosed_Ici.preimage hFcont)
  have hAbdd : ∀ x, BddBelow (A x) := fun x => hK.bddBelow.mono inter_subset_left
  have hgx : ∀ x, 0 < x → g x = sInf (A x) := fun x hx => by simp [g, hx]
  have hgA : ∀ x ∈ Ioc 0 r, g x ∈ A x := fun x hx => by
    rw [hgx x hx.1]
    exact (hAcl x).csInf_mem (hAne x hx.2) (hAbdd x)
  have hFg : ∀ x ∈ Ioc 0 r, F (g x) ≤ x := by
    intro x hx
    by_contra hlt
    rw [not_le] at hlt
    set s := g x - (F (g x) - x) / 2 with hs
    have hFs : x < F s := by
      have := hFle s (g x) (by linarith)
      linarith
    have hne' : (K ∩ Iic s).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp only [F, h, measure_empty, ENNReal.toReal_zero] at hFs
      linarith [hx.1]
    have hc' : IsCompact (K ∩ Iic s) := hK.inter_right isClosed_Iic
    have hs'mem : sSup (K ∩ Iic s) ∈ K ∩ Iic s := hc'.sSup_mem hne'
    have hFs' : F (sSup (K ∩ Iic s)) = F s := by
      have : K ∩ Iic (sSup (K ∩ Iic s)) = K ∩ Iic s := by
        ext y
        constructor
        · rintro ⟨hyK, hy⟩
          exact ⟨hyK, le_trans (mem_Iic.1 hy) (mem_Iic.1 hs'mem.2)⟩
        · rintro hy
          exact ⟨hy.1, le_csSup hc'.bddAbove hy⟩
      simp only [F, this]
    have hmem : sSup (K ∩ Iic s) ∈ A x := ⟨hs'mem.1, by
      change x ≤ F (sSup (K ∩ Iic s))
      linarith⟩
    have h1 := csInf_le (hAbdd x) hmem
    rw [← hgx x hx.1] at h1
    linarith [mem_Iic.1 hs'mem.2]
  have hFa : F a = 0 := by
    have : K ∩ Iic a = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun hy => hKa hy
    simp [F, this]
  refine ⟨g, by simp [g], fun x hx => (hgA x hx).1, ?_⟩
  intro x hx x' hx' hlt
  have hx0 : 0 < x := hx'.1.trans_lt hlt
  have hgx' := hgA x ⟨hx0, hx.2⟩
  have hxF : x ≤ F (g x) := hgx'.2
  rcases hx'.1.eq_or_lt with h0 | hpos
  · subst h0
    have hga : g 0 = a := by simp [g]
    rw [hga]
    have hax : a ≤ g x := (hKa hgx'.1).le
    have := hFle a (g x) hax
    linarith
  · have h1 := hFg x' ⟨hpos, hx'.2⟩
    have hle : g x' ≤ g x := by
      by_contra h
      rw [not_le] at h
      have := hFmono h.le
      linarith
    have := hFle (g x') (g x) hle
    linarith

/-- Mirror image of `exists_arm_right`: a compact set `K ⊆ (-∞, a)` of measure at least `r`
receives a map `g` with `g 0 = a` that expands distances on `[-r, 0]` and sends `[-r, 0)`
into `K`. -/
private theorem exists_arm_left {K : Set ℝ} (hK : IsCompact K) {a r : ℝ}
    (hKa : K ⊆ Iio a) (hKr : ENNReal.ofReal r ≤ volume K) :
    ∃ g : ℝ → ℝ, g 0 = a ∧ (∀ x ∈ Ico (-r) 0, g x ∈ K) ∧
      ∀ x ∈ Icc (-r) 0, ∀ x' ∈ Icc (-r) 0, x' < x → x - x' ≤ g x - g x' := by
  have hK' : IsCompact (Neg.neg ⁻¹' K) := (Homeomorph.neg ℝ).isCompact_preimage.2 hK
  have hKa' : Neg.neg ⁻¹' K ⊆ Ioi (-a) := fun y hy => by
    have := hKa hy
    simp only [mem_Iio] at this
    simp only [mem_Ioi]
    linarith
  have hvol : volume (Neg.neg ⁻¹' K) = volume K :=
    (Measure.measurePreserving_neg volume).measure_preimage hK.measurableSet.nullMeasurableSet
  obtain ⟨g, hg0, hgK, hge⟩ := exists_arm_right hK' hKa' (hvol ▸ hKr)
  refine ⟨fun x => -g (-x), by simp [hg0], fun x hx => ?_, fun x hx x' hx' hlt => ?_⟩
  · have := hgK (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa using this
  · have := hge (-x') ⟨by linarith [hx'.2], by linarith [hx'.1]⟩ (-x)
      ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
    linarith

/-- A measurable set `H ⊆ ℝ` of finite measure with more than `r` of `H` on each side of a point
`a ∈ H` receives a map `g` with `g 0 = a` that expands distances on `[-r, r]` and sends `[-r, r]`
into `H`. -/
private theorem exists_arm {H : Set ℝ} (hH : MeasurableSet H) (hHf : volume H ≠ ∞) {a r : ℝ}
    (haH : a ∈ H) (hright : ENNReal.ofReal r < volume (H ∩ Ioi a))
    (hleft : ENNReal.ofReal r < volume (H ∩ Iio a)) :
    ∃ g : ℝ → ℝ, g 0 = a ∧ (∀ x ∈ Icc (-r) r, g x ∈ H) ∧
      ∀ x ∈ Icc (-r) r, ∀ x' ∈ Icc (-r) r, x' < x → x - x' ≤ g x - g x' := by
  obtain ⟨K₁, hK₁H, hK₁c, hK₁r⟩ := (hH.inter measurableSet_Ioi).exists_lt_isCompact_of_ne_top
    (measure_ne_top_of_subset inter_subset_left hHf) hright
  obtain ⟨K₂, hK₂H, hK₂c, hK₂r⟩ := (hH.inter measurableSet_Iio).exists_lt_isCompact_of_ne_top
    (measure_ne_top_of_subset inter_subset_left hHf) hleft
  obtain ⟨g₁, hg₁0, hg₁K, hg₁e⟩ := exists_arm_right hK₁c (hK₁H.trans inter_subset_right) hK₁r.le
  obtain ⟨g₂, hg₂0, hg₂K, hg₂e⟩ := exists_arm_left hK₂c (hK₂H.trans inter_subset_right) hK₂r.le
  classical
  refine ⟨fun x => if 0 ≤ x then g₁ x else g₂ x, by simp [hg₁0], fun x hx => ?_,
    fun x hx x' hx' hlt => ?_⟩
  · by_cases h0 : 0 ≤ x
    · rcases h0.eq_or_lt with rfl | hpos
      · simp [hg₁0, haH]
      · simp only [h0, ite_true]
        exact (hK₁H (hg₁K x ⟨hpos, hx.2⟩)).1
    · simp only [h0, ite_false]
      exact (hK₂H (hg₂K x ⟨hx.1, not_le.1 h0⟩)).1
  · by_cases h0 : 0 ≤ x'
    · have h0x : 0 ≤ x := h0.trans hlt.le
      simp only [h0, h0x, ite_true]
      exact hg₁e x ⟨h0x, hx.2⟩ x' ⟨h0, hx'.2⟩ hlt
    · by_cases h1 : 0 ≤ x
      · simp only [h0, h1, ite_true, ite_false]
        have e1 : x - 0 ≤ g₁ x - g₁ 0 := by
          rcases h1.eq_or_lt with rfl | hpos
          · simp
          · exact hg₁e x ⟨h1, hx.2⟩ 0 ⟨le_rfl, h1.trans hx.2⟩ hpos
        have e2 : 0 - x' ≤ g₂ 0 - g₂ x' :=
          hg₂e 0 ⟨by linarith [hx'.1, not_le.1 h0], le_rfl⟩ x' ⟨hx'.1, (not_le.1 h0).le⟩
            (not_le.1 h0)
        rw [hg₁0] at e1
        rw [hg₂0] at e2
        linarith
      · simp only [h0, h1, ite_false]
        exact hg₂e x ⟨hx.1, (not_le.1 h1).le⟩ x' ⟨hx'.1, (not_le.1 h0).le⟩ hlt

/-- A measurable set `T ⊆ [0, n]²` in which every point has at most `R` of `T` on one of its four
sides, along its row or along its column, has measure at most `4 R n`. -/
private theorem volume_le_of_room {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) {n : ℝ}
    (hTn : T ⊆ Icc 0 n ×ˢ Icc 0 n) (R : ℝ≥0∞)
    (hroom : ∀ p ∈ T, volume {x | (x, p.2) ∈ T ∧ p.1 < x} ≤ R ∨
      volume {x | (x, p.2) ∈ T ∧ x < p.1} ≤ R ∨ volume {y | (p.1, y) ∈ T ∧ p.2 < y} ≤ R ∨
      volume {y | (p.1, y) ∈ T ∧ y < p.2} ≤ R) :
    volume T ≤ 4 * R * ENNReal.ofReal n := by
  have hmR : Measurable fun p : ℝ × ℝ => volume {x | (x, p.2) ∈ T ∧ p.1 < x} :=
    measurable_measure_prodMk_left (s := {q : (ℝ × ℝ) × ℝ | (q.2, q.1.2) ∈ T ∧ q.1.1 < q.2})
      ((hT.preimage (by fun_prop)).inter (measurableSet_lt (f := fun q : (ℝ × ℝ) × ℝ => q.1.1)
        (g := fun q => q.2) (by fun_prop) (by fun_prop)))
  have hmL : Measurable fun p : ℝ × ℝ => volume {x | (x, p.2) ∈ T ∧ x < p.1} :=
    measurable_measure_prodMk_left (s := {q : (ℝ × ℝ) × ℝ | (q.2, q.1.2) ∈ T ∧ q.2 < q.1.1})
      ((hT.preimage (by fun_prop)).inter (measurableSet_lt (f := fun q : (ℝ × ℝ) × ℝ => q.2)
        (g := fun q => q.1.1) (by fun_prop) (by fun_prop)))
  have hmU : Measurable fun p : ℝ × ℝ => volume {y | (p.1, y) ∈ T ∧ p.2 < y} :=
    measurable_measure_prodMk_left (s := {q : (ℝ × ℝ) × ℝ | (q.1.1, q.2) ∈ T ∧ q.1.2 < q.2})
      ((hT.preimage (by fun_prop)).inter (measurableSet_lt (f := fun q : (ℝ × ℝ) × ℝ => q.1.2)
        (g := fun q => q.2) (by fun_prop) (by fun_prop)))
  have hmD : Measurable fun p : ℝ × ℝ => volume {y | (p.1, y) ∈ T ∧ y < p.2} :=
    measurable_measure_prodMk_left (s := {q : (ℝ × ℝ) × ℝ | (q.1.1, q.2) ∈ T ∧ q.2 < q.1.2})
      ((hT.preimage (by fun_prop)).inter (measurableSet_lt (f := fun q : (ℝ × ℝ) × ℝ => q.2)
        (g := fun q => q.1.2) (by fun_prop) (by fun_prop)))
  set Bh := {p : ℝ × ℝ | p ∈ T ∧ (volume {x | (x, p.2) ∈ T ∧ p.1 < x} ≤ R ∨
    volume {x | (x, p.2) ∈ T ∧ x < p.1} ≤ R)} with hBh_def
  set Bv := {p : ℝ × ℝ | p ∈ T ∧ (volume {y | (p.1, y) ∈ T ∧ p.2 < y} ≤ R ∨
    volume {y | (p.1, y) ∈ T ∧ y < p.2} ≤ R)} with hBv_def
  have hBh : MeasurableSet Bh :=
    hT.inter ((measurableSet_le hmR measurable_const).union (measurableSet_le hmL measurable_const))
  have hBv : MeasurableSet Bv :=
    hT.inter ((measurableSet_le hmU measurable_const).union (measurableSet_le hmD measurable_const))
  have hTB : T ⊆ Bh ∪ Bv := fun p hp => by
    rcases hroom p hp with h | h | h | h
    · exact Or.inl ⟨hp, Or.inl h⟩
    · exact Or.inl ⟨hp, Or.inr h⟩
    · exact Or.inr ⟨hp, Or.inl h⟩
    · exact Or.inr ⟨hp, Or.inr h⟩
  have hsec_h : ∀ y,
      volume ((fun x => (x, y)) ⁻¹' Bh) ≤ (Icc 0 n).indicator (fun _ => 2 * R) y := by
    intro y
    by_cases hy : y ∈ Icc 0 n
    · rw [indicator_of_mem hy]
      set H := {x | (x, y) ∈ T}
      have hHb : BddBelow H := ⟨0, fun x hx => (hTn hx).1.1⟩
      have hHa : BddAbove H := ⟨n, fun x hx => (hTn hx).1.2⟩
      calc volume ((fun x => (x, y)) ⁻¹' Bh)
          ≤ volume ({a | a ∈ H ∧ volume (H ∩ Ioi a) ≤ R} ∪
              {a | a ∈ H ∧ volume (H ∩ Iio a) ≤ R}) := by
            refine measure_mono fun x hx => ?_
            rcases hx with ⟨hxT, h | h⟩
            · exact Or.inl ⟨hxT, h⟩
            · exact Or.inr ⟨hxT, h⟩
        _ ≤ R + R := (measure_union_le _ _).trans
            (add_le_add (volume_room_right_le hHb R) (volume_room_left_le hHa R))
        _ = 2 * R := (two_mul R).symm
    · rw [indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' Bh = ∅ :=
        eq_empty_of_forall_notMem fun x hx => hy (hTn hx.1).2
      simp [this]
  have hsec_v : ∀ x, volume (Prod.mk x ⁻¹' Bv) ≤ (Icc 0 n).indicator (fun _ => 2 * R) x := by
    intro x
    by_cases hx : x ∈ Icc 0 n
    · rw [indicator_of_mem hx]
      set V := {y | (x, y) ∈ T}
      have hVb : BddBelow V := ⟨0, fun y hy => (hTn hy).2.1⟩
      have hVa : BddAbove V := ⟨n, fun y hy => (hTn hy).2.2⟩
      calc volume (Prod.mk x ⁻¹' Bv)
          ≤ volume ({a | a ∈ V ∧ volume (V ∩ Ioi a) ≤ R} ∪
              {a | a ∈ V ∧ volume (V ∩ Iio a) ≤ R}) := by
            refine measure_mono fun y hy => ?_
            rcases hy with ⟨hyT, h | h⟩
            · exact Or.inl ⟨hyT, h⟩
            · exact Or.inr ⟨hyT, h⟩
        _ ≤ R + R := (measure_union_le _ _).trans
            (add_le_add (volume_room_right_le hVb R) (volume_room_left_le hVa R))
        _ = 2 * R := (two_mul R).symm
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' Bv = ∅ :=
        eq_empty_of_forall_notMem fun y hy => hx (hTn hy.1).1
      simp [this]
  have hvol_h : volume Bh ≤ 2 * R * ENNReal.ofReal n := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hBh]
    calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' Bh)
        ≤ ∫⁻ y, (Icc 0 n).indicator (fun _ => 2 * R) y := lintegral_mono hsec_h
      _ = 2 * R * volume (Icc 0 n) := lintegral_indicator_const measurableSet_Icc _
      _ = 2 * R * ENNReal.ofReal n := by rw [Real.volume_Icc, sub_zero]
  have hvol_v : volume Bv ≤ 2 * R * ENNReal.ofReal n := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hBv]
    calc ∫⁻ x, volume (Prod.mk x ⁻¹' Bv)
        ≤ ∫⁻ x, (Icc 0 n).indicator (fun _ => 2 * R) x := lintegral_mono hsec_v
      _ = 2 * R * volume (Icc 0 n) := lintegral_indicator_const measurableSet_Icc _
      _ = 2 * R * ENNReal.ofReal n := by rw [Real.volume_Icc, sub_zero]
  calc volume T ≤ volume (Bh ∪ Bv) := measure_mono hTB
    _ ≤ volume Bh + volume Bv := measure_union_le _ _
    _ ≤ 2 * R * ENNReal.ofReal n + 2 * R * ENNReal.ofReal n := add_le_add hvol_h hvol_v
    _ = 4 * R * ENNReal.ofReal n := by ring

/-- Consecutive gaps of at least `c` give gaps of at least `(j - i) c`. -/
private theorem gap_chain {t : ℕ} (z : Fin t → ℝ) (c : ℝ)
    (h : ∀ i j : Fin t, (j : ℕ) = i + 1 → z i + c ≤ z j) :
    ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j := by
  suffices H : ∀ d : ℕ, ∀ i j : Fin t, (j : ℕ) = i + d → z i + (d : ℝ) * c ≤ z j by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := le_of_lt hij
    have := H ((j : ℕ) - i) i j (by omega)
    rwa [Nat.cast_sub hij'] at this
  intro d
  induction d with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by omega)
    simp [this]
  | succ d ih =>
    intro i j hij
    have hlt : (i : ℕ) + d < t := by omega
    have h1 := ih i ⟨i + d, hlt⟩ rfl
    have h2 := h ⟨i + d, hlt⟩ j (by simp only; omega)
    push_cast
    linarith

/-- A set `U ⊆ [0, n]` of measure `m` contains a box of `t`-tuples with gaps of at least `c`,
of measure at least `(m / t - c)^t`. -/
private theorem volume_gaps_ge {U : Set ℝ} {n : ℝ} (hUn : U ⊆ Icc 0 n)
    {t : ℕ} (ht : 1 ≤ t) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal ((volume U).toReal / t - c) ^ t ≤
      volume {z : Fin t → ℝ | (∀ i, z i ∈ U) ∧
        ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j} := by
  set m := (volume U).toReal with hm
  have hUfin : volume U ≠ ∞ := measure_ne_top_of_subset hUn (by simp [Real.volume_Icc])
  rcases le_or_gt (m / t - c) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos hneg, zero_pow (by omega)]
    exact zero_le
  have hn : 0 ≤ n := by
    by_contra hn
    have : U = ∅ := eq_empty_of_forall_notMem fun x hx => hn ((hUn hx).1.trans (hUn hx).2)
    simp [m, this] at hpos
    have : (0 : ℝ) < t := by exact_mod_cast ht
    linarith
  set F : ℝ → ℝ := fun a => (volume (U ∩ Iio a)).toReal with hF
  have hfin : ∀ a, volume (U ∩ Iio a) ≠ ∞ := fun a =>
    measure_ne_top_of_subset inter_subset_left hUfin
  have hFle : ∀ a' a, a' ≤ a → F a ≤ F a' + (a - a') := by
    intro a' a haa
    have h1 : U ∩ Iio a ⊆ (U ∩ Iio a') ∪ Ico a' a := fun y hy => by
      by_cases hy' : y < a'
      · exact Or.inl ⟨hy.1, hy'⟩
      · exact Or.inr ⟨not_lt.1 hy', hy.2⟩
    have h2 := (measure_mono (μ := volume) h1).trans (measure_union_le _ _)
    rw [Real.volume_Ico] at h2
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin a', ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add (hfin a') ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h3
  have hFmono : Monotone F := fun a' a haa => ENNReal.toReal_mono (hfin a)
    (measure_mono (μ := volume) (inter_subset_inter_right _ (Iio_subset_Iio haa)))
  have hFcont : Continuous F := by
    refine (LipschitzWith.of_le_add fun s s' => ?_).continuous
    rcases le_total s' s with h | h
    · have := hFle s' s h
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    · have := hFmono h
      linarith [dist_nonneg (x := s) (y := s')]
  have hF0 : F 0 = 0 := by
    have : U ∩ Iio 0 = ∅ := eq_empty_of_forall_notMem fun x hx =>
      absurd (hUn hx.1).1 (not_le.2 hx.2)
    simp [F, this]
  have hFn : F (n + 1) = m := by
    have : U ∩ Iio (n + 1) = U := inter_eq_left.2 fun x hx => by
      simp only [mem_Iio]
      linarith [(hUn hx).2]
    simp [F, this, m]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hsplit : ∀ k : ℕ, k ≤ t → ∃ a ∈ Icc 0 (n + 1), F a = k * m / t := fun k hk => by
    refine intermediate_value_Icc (by linarith) hFcont.continuousOn ⟨?_, ?_⟩
    · rw [hF0]
      positivity
    · rw [hFn, div_le_iff₀ htpos]
      have : (k : ℝ) ≤ t := by exact_mod_cast hk
      nlinarith
  choose! α hα using hsplit
  set Ui : Fin t → Set ℝ := fun k => U ∩ Ico (α k) (α ((k : ℕ) + 1) - c) with hUi_def
  have hUi : ∀ k : Fin t, ENNReal.ofReal (m / t - c) ≤ volume (Ui k) := by
    intro k
    have hk1 : (k : ℕ) + 1 ≤ t := k.2
    have hk0 : (k : ℕ) ≤ t := k.2.le
    have hFa1 := (hα _ hk1).2
    have hFa0 := (hα _ hk0).2
    have h1 : U ∩ Iio (α ((k : ℕ) + 1) - c) ⊆ Ui k ∪ (U ∩ Iio (α k)) := fun y hy => by
      by_cases hy' : y < α k
      · exact Or.inr ⟨hy.1, hy'⟩
      · exact Or.inl ⟨hy.1, not_lt.1 hy', hy.2⟩
    have hUifin : volume (Ui k) ≠ ∞ := measure_ne_top_of_subset inter_subset_left hUfin
    have h2 := (measure_mono (μ := volume) h1).trans (measure_union_le _ _)
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hUifin, hfin _⟩) h2
    rw [ENNReal.toReal_add hUifin (hfin _)] at h3
    have h4 := hFle (α ((k : ℕ) + 1) - c) (α ((k : ℕ) + 1)) (by linarith)
    change F (α ((k : ℕ) + 1) - c) ≤ (volume (Ui k)).toReal + F (α k) at h3
    rw [← ENNReal.ofReal_toReal hUifin]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hFa1] at h4
    rw [hFa0] at h3
    push_cast at h4
    have : ((k : ℝ) + 1) * m / t = k * m / t + m / t := by ring
    linarith
  have hbox : univ.pi Ui ⊆ {z : Fin t → ℝ | (∀ i, z i ∈ U) ∧
      ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j} := by
    intro z hz
    have hz' : ∀ k, z k ∈ Ui k := fun k => hz k (mem_univ k)
    refine ⟨fun i => (hz' i).1, gap_chain z c fun i j hij => ?_⟩
    have h1 := (hz' i).2.2
    have h2 := (hz' j).2.1
    rw [hij] at h2
    linarith
  calc ENNReal.ofReal (m / t - c) ^ t = ∏ _k : Fin t, ENNReal.ofReal (m / t - c) := by simp
    _ ≤ ∏ k, volume (Ui k) := Finset.prod_le_prod fun k _ => hUi k
    _ = volume (univ.pi Ui) := (volume_pi_pi Ui).symm
    _ ≤ _ := measure_mono hbox

/-- Two expanding arms through `(a, b)` that lie in every horizontal slice at the heights `z i`
(with gaps of at least `c`) give a copy of the stacked plus sign. -/
private theorem containsPatternD_of_arms {S : Set (Fin 3 → ℝ)} {t : ℕ} {r c : ℝ} (hc : 0 < c)
    {z : Fin t → ℝ} (hz : ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j)
    {a b : ℝ} {gh gv : ℝ → ℝ} (hgh0 : gh 0 = a) (hgv0 : gv 0 = b)
    (hgh : ∀ x ∈ Icc (-r) r, ∀ i, ![gh x, b, z i] ∈ S)
    (hgv : ∀ y ∈ Icc (-r) r, ∀ i, ![a, gv y, z i] ∈ S)
    (hghe : ∀ x ∈ Icc (-r) r, ∀ x' ∈ Icc (-r) r, x' < x → x - x' ≤ gh x - gh x')
    (hgve : ∀ y ∈ Icc (-r) r, ∀ y' ∈ Icc (-r) r, y' < y → y - y' ≤ gv y - gv y') :
    ContainsPatternD S {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c} := by
  classical
  let f2 : ℝ → ℝ := fun s => if h : ⌊s / c⌋₊ - 1 < t then z ⟨⌊s / c⌋₊ - 1, h⟩ else 0
  have hf2 : ∀ i : ℕ, (hi1 : 1 ≤ i) → (hit : i ≤ t) → f2 (i * c) = z ⟨i - 1, by omega⟩ := by
    intro i hi1 hit
    have : ⌊(i : ℝ) * c / c⌋₊ = i := by
      rw [mul_div_cancel_right₀ _ hc.ne']
      exact Nat.floor_natCast i
    simp only [f2, this]
    exact dite_eq_left (by omega)
  refine ⟨![gh, gv, f2], ?_, ?_⟩
  · intro k
    fin_cases k
    · rintro p ⟨hp0, -, -, -⟩ q ⟨hq0, -, -, -⟩ hlt
      exact hghe _ (abs_le.1 hp0) _ (abs_le.1 hq0) hlt
    · rintro p ⟨-, hp1, -, -⟩ q ⟨-, hq1, -, -⟩ hlt
      exact hgve _ (abs_le.1 hp1) _ (abs_le.1 hq1) hlt
    · rintro p ⟨-, -, -, i, hi1, hit, hpi⟩ q ⟨-, -, -, i', hi1', hit', hqi⟩ hlt
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] at hlt ⊢
      rw [hpi, hqi] at hlt ⊢
      have hii : i' < i := by exact_mod_cast lt_of_mul_lt_mul_right hlt hc.le
      rw [hf2 i hi1 hit, hf2 i' hi1' hit']
      have := hz ⟨i' - 1, by omega⟩ ⟨i - 1, by omega⟩ (by simp only [Fin.mk_lt_mk]; omega)
      simp only at this
      rw [Nat.cast_sub hi1, Nat.cast_sub hi1'] at this
      push_cast at this
      linarith
  · rintro p ⟨hp0, hp1, h01, i, hi1, hit, hpi⟩
    have hp : (fun k => (![gh, gv, f2] : Fin 3 → ℝ → ℝ) k (p k)) =
        ![gh (p 0), gv (p 1), z ⟨i - 1, by omega⟩] := by
      funext k
      fin_cases k
      · rfl
      · rfl
      · simp [hpi, hf2 i hi1 hit]
    rw [hp]
    rcases h01 with h0 | h1
    · rw [h0, hgh0]
      exact hgv _ (abs_le.1 hp1) _
    · rw [h1, hgv0]
      exact hgh _ (abs_le.1 hp0) _

/-- Every point of a horizontal slice `{p | ∀ i, (p, z i) ∈ S}` of a pattern-free set, with
`z` having gaps of at least `c`, has at most `r` of the slice on one of its four sides. -/
private theorem room_of_free {t : ℕ} {r c : ℝ} (hc : 0 < c) {S : Set (Fin 3 → ℝ)}
    (hfree : ¬ ContainsPatternD S {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c})
    {z : Fin t → ℝ} (hz : ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j)
    {T : Set (ℝ × ℝ)} (hTdef : ∀ p, p ∈ T ↔ ∀ i, ![p.1, p.2, z i] ∈ S) (hT : MeasurableSet T)
    (hTf : ∀ y, volume {x | (x, y) ∈ T} ≠ ∞) (hTf' : ∀ x, volume {y | (x, y) ∈ T} ≠ ∞) :
    ∀ p ∈ T, volume {x | (x, p.2) ∈ T ∧ p.1 < x} ≤ ENNReal.ofReal r ∨
      volume {x | (x, p.2) ∈ T ∧ x < p.1} ≤ ENNReal.ofReal r ∨
      volume {y | (p.1, y) ∈ T ∧ p.2 < y} ≤ ENNReal.ofReal r ∨
      volume {y | (p.1, y) ∈ T ∧ y < p.2} ≤ ENNReal.ofReal r := by
  rintro ⟨a, b⟩ hp
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨gh, hgh0, hghH, hghe⟩ := exists_arm (H := {x | (x, b) ∈ T})
    (hT.preimage (by fun_prop)) (hTf b) hp h1 h2
  obtain ⟨gv, hgv0, hgvV, hgve⟩ := exists_arm (H := {y | (a, y) ∈ T})
    (hT.preimage (by fun_prop)) (hTf' a) hp h3 h4
  exact hfree (containsPatternD_of_arms hc hz hgh0 hgv0
    (fun x hx i => (hTdef _).1 (hghH x hx) i) (fun y hy i => (hTdef _).1 (hgvV y hy) i)
    hghe hgve)

/-- The upper bound for one open pattern-free set, before taking the supremum. -/
private theorem volume_le_of_free {t : ℕ} (ht : 2 ≤ t) {r c n : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hn : 0 < n) {S : Set (Fin 3 → ℝ)} (hS : IsOpen S) (hSn : S ⊆ Icc 0 (fun _ => n))
    (hfree : ¬ ContainsPatternD S {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c}) :
    volume.real S ≤ t * c * n ^ 2 + t * (4 * r) ^ (1 / t : ℝ) * n ^ (3 - 1 / t : ℝ) := by
  set Φ : (ℝ × ℝ) × ℝ → Fin 3 → ℝ := fun q => ![q.1.1, q.1.2, q.2] with hΦ_def
  have hΦ : MeasurePreserving Φ volume volume := measurePreserving_vec3
  have hSm : MeasurableSet S := hS.measurableSet
  have hmem : ∀ {x y z : ℝ}, ![x, y, z] ∈ S → x ∈ Icc 0 n ∧ y ∈ Icc 0 n ∧ z ∈ Icc 0 n := by
    intro x y z h
    have h' := hSn h
    exact ⟨⟨h'.1 0, h'.2 0⟩, ⟨h'.1 1, h'.2 1⟩, ⟨h'.1 2, h'.2 2⟩⟩
  set m : ℝ × ℝ → ℝ≥0∞ := fun p => volume {s : ℝ | Φ (p, s) ∈ S} with hm_def
  have hvolS : volume S = ∫⁻ p, m p := by
    rw [← hΦ.measure_preimage hSm.nullMeasurableSet, Measure.volume_eq_prod (ℝ × ℝ) ℝ,
      Measure.prod_apply (hΦ.measurable hSm)]
    rfl
  set W : Set ((ℝ × ℝ) × (Fin t → ℝ)) := {q | (∀ i, Φ (q.1, q.2 i) ∈ S) ∧
    ∀ i j : Fin t, i < j → q.2 i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ q.2 j} with hW_def
  have hWm : MeasurableSet W := by
    have : W = (⋂ i, {q : (ℝ × ℝ) × (Fin t → ℝ) | Φ (q.1, q.2 i) ∈ S}) ∩
        ⋂ i, ⋂ j, {q : (ℝ × ℝ) × (Fin t → ℝ) | i < j →
          q.2 i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ q.2 j} := by
      ext q
      simp [W]
    rw [this]
    refine (MeasurableSet.iInter fun i => ?_).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    · exact hSm.preimage (hΦ.measurable.comp (by fun_prop))
    · by_cases hij : i < j
      · simp only [hij, true_imp_iff]
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · simp [hij]
  have hW_ge : ∫⁻ p, ENNReal.ofReal ((m p).toReal / t - c) ^ t ≤ volume W := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (Fin t → ℝ), Measure.prod_apply hWm]
    refine lintegral_mono fun p => ?_
    have hUn : {s : ℝ | Φ (p, s) ∈ S} ⊆ Icc 0 n := fun s hs => (hmem hs).2.2
    exact volume_gaps_ge hUn (by omega) hc.le
  have hW_le : volume W ≤ 4 * ENNReal.ofReal r * ENNReal.ofReal n * ENNReal.ofReal n ^ t := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (Fin t → ℝ), Measure.prod_apply_symm hWm]
    have hbox : MeasurableSet (univ.pi fun _ : Fin t => Icc 0 n) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Icc
    calc ∫⁻ z, volume ((fun p => (p, z)) ⁻¹' W)
        ≤ ∫⁻ z, (univ.pi fun _ : Fin t => Icc 0 n).indicator
            (fun _ => 4 * ENNReal.ofReal r * ENNReal.ofReal n) z := lintegral_mono fun z => ?_
      _ = 4 * ENNReal.ofReal r * ENNReal.ofReal n * volume (univ.pi fun _ : Fin t => Icc 0 n) :=
          lintegral_indicator_const hbox _
      _ = 4 * ENNReal.ofReal r * ENNReal.ofReal n * ENNReal.ofReal n ^ t := by
          rw [volume_pi_pi]
          simp [Real.volume_Icc]
    have ht0 : (0 : ℕ) < t := by omega
    by_cases hz : z ∈ univ.pi fun _ : Fin t => Icc 0 n
    · rw [indicator_of_mem hz]
      by_cases hgap : ∀ i j : Fin t, i < j → z i + (((j : ℕ) : ℝ) - (i : ℕ)) * c ≤ z j
      · set T := (fun p => (p, z)) ⁻¹' W with hT_def
        have hTdef : ∀ p, p ∈ T ↔ ∀ i, ![p.1, p.2, z i] ∈ S := fun p =>
          ⟨fun h => h.1, fun h => ⟨h, hgap⟩⟩
        have hTm : MeasurableSet T := hWm.preimage (by fun_prop)
        have hTn : T ⊆ Icc 0 n ×ˢ Icc 0 n := fun p hp => by
          have := hmem ((hTdef p).1 hp ⟨0, ht0⟩)
          exact ⟨this.1, this.2.1⟩
        have hTf : ∀ y, volume {x | (x, y) ∈ T} ≠ ∞ := fun y =>
          measure_ne_top_of_subset (s := Icc 0 n) (fun x hx => (hTn hx).1)
            (by simp [Real.volume_Icc])
        have hTf' : ∀ x, volume {y | (x, y) ∈ T} ≠ ∞ := fun x =>
          measure_ne_top_of_subset (s := Icc 0 n) (fun y hy => (hTn hy).2)
            (by simp [Real.volume_Icc])
        exact volume_le_of_room hTm hTn _ (room_of_free hc hfree hgap hTdef hTm hTf hTf')
      · have : (fun p => (p, z)) ⁻¹' W = ∅ := eq_empty_of_forall_notMem fun p hp => hgap hp.2
        simp [this]
    · rw [indicator_of_notMem hz]
      have : (fun p => (p, z)) ⁻¹' W = ∅ := eq_empty_of_forall_notMem fun p hp =>
        hz fun i _ => (hmem (hp.1 i)).2.2
      simp [this]
  set A : Set (ℝ × ℝ) := Icc 0 n ×ˢ Icc 0 n with hA_def
  have hvolA : volume A = ENNReal.ofReal (n ^ 2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul hn.le, sq]
  set h : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((m p).toReal / t - c) with hh_def
  have hmeas_m : Measurable m := measurable_measure_prodMk_left (hΦ.measurable hSm)
  have hmeas_h : Measurable h :=
    ENNReal.measurable_ofReal.comp ((hmeas_m.ennreal_toReal.div_const _).sub_const _)
  have hm_fin : ∀ p, m p ≤ ENNReal.ofReal n := fun p =>
    (measure_mono (μ := volume) (s := {s : ℝ | Φ (p, s) ∈ S}) (t := Icc 0 n)
      (fun s hs => (hmem hs).2.2)).trans (by rw [Real.volume_Icc, sub_zero])
  have hm_supp : Function.support m ⊆ A := by
    intro p hp
    by_contra hpA
    have : {s : ℝ | Φ (p, s) ∈ S} = ∅ :=
      eq_empty_of_forall_notMem fun s hs => hpA ⟨(hmem hs).1, (hmem hs).2.1⟩
    exact hp (by simp [m, this])
  have htpos : (0 : ℝ) < t := by positivity
  have hm_le : ∀ p, m p ≤ t * (h p + ENNReal.ofReal c) := by
    intro p
    have hfin : m p ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hm_fin p)
    have hhfin : h p ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hhfin, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hc.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hh_def, ENNReal.toReal_ofReal']
    calc (m p).toReal = t * ((m p).toReal / t - c + c) := by field_simp; ring
      _ ≤ t * (max ((m p).toReal / t - c) 0 + c) := by gcongr; exact le_max_left _ _
  have hint1 : ∫⁻ p, m p ≤ t * ((∫⁻ p in A, h p) + ENNReal.ofReal c * ENNReal.ofReal (n ^ 2)) := by
    rw [← setLIntegral_eq_of_support_subset hm_supp]
    calc ∫⁻ p in A, m p ≤ ∫⁻ p in A, t * (h p + ENNReal.ofReal c) := lintegral_mono fun p => hm_le p
      _ = t * ((∫⁻ p in A, h p) + ENNReal.ofReal c * ENNReal.ofReal (n ^ 2)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top t),
          lintegral_add_right _ measurable_const, setLIntegral_const, hvolA]
  have ht1 : (1 : ℝ) < t := by exact_mod_cast ht
  have hq : (t : ℝ).HolderConjugate ((t : ℝ) / (t - 1)) := .conjExponent ht1
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict A) hq
    hmeas_h.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at hHolder
  have hY : ∫⁻ a in A, h a ^ (t : ℝ) ≤ ENNReal.ofReal (4 * r * n ^ (t + 1)) := by
    calc ∫⁻ a in A, h a ^ (t : ℝ) ≤ ∫⁻ a, h a ^ (t : ℝ) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ a, h a ^ t := by simp_rw [ENNReal.rpow_natCast]
      _ ≤ volume W := hW_ge
      _ ≤ 4 * ENNReal.ofReal r * ENNReal.ofReal n * ENNReal.ofReal n ^ t := hW_le
      _ = ENNReal.ofReal (4 * r * n ^ (t + 1)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hn.le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hX : ∫⁻ a in A, h a ≤ ENNReal.ofReal ((4 * r * n ^ (t + 1)) ^ (1 / t : ℝ) *
      (n ^ 2) ^ (1 / (t / (t - 1)) : ℝ)) := by
    refine hHolder.trans ?_
    rw [hvolA, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
  have hfinal : volume S ≤ ENNReal.ofReal (t * ((4 * r * n ^ (t + 1)) ^ (1 / t : ℝ) *
      (n ^ 2) ^ (1 / (t / (t - 1)) : ℝ) + c * n ^ 2)) := by
    rw [hvolS]
    refine hint1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hc.le]
    gcongr
  have hreal : volume.real S ≤ t * ((4 * r * n ^ (t + 1)) ^ (1 / t : ℝ) *
      (n ^ 2) ^ (1 / (t / (t - 1)) : ℝ) + c * n ^ 2) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hfinal
  have hB : (4 * r * n ^ (t + 1)) ^ (1 / t : ℝ) * (n ^ 2) ^ (1 / (t / (t - 1)) : ℝ) =
      (4 * r) ^ (1 / t : ℝ) * n ^ (3 - 1 / t : ℝ) := by
    have ht0 : (t : ℝ) ≠ 0 := htpos.ne'
    have ht1' : (t : ℝ) - 1 ≠ 0 := by linarith
    rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]
    congr 1
    rw [← Real.rpow_natCast n (t + 1), ← Real.rpow_natCast n 2, ← Real.rpow_mul hn.le,
      ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    push_cast
    field_simp
    ring
  rw [hB] at hreal
  calc volume.real S ≤ t * ((4 * r) ^ (1 / t : ℝ) * n ^ (3 - 1 / t : ℝ) + c * n ^ 2) := hreal
    _ = t * c * n ^ 2 + t * (4 * r) ^ (1 / t : ℝ) * n ^ (3 - 1 / t : ℝ) := by ring


private theorem floor_lt_floor_of_add_le {a b u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) (hab : a + u ≤ b) :
    ⌊a / u⌋₊ < ⌊b / u⌋₊ := by
  have h1 : a / u + 1 ≤ b / u := by
    rw [div_add_one hu.ne', div_le_div_iff_of_pos_right hu]
    exact hab
  calc ⌊a / u⌋₊ < ⌊a / u⌋₊ + 1 := Nat.lt_succ_self _
    _ = ⌊a / u + 1⌋₊ := (Nat.floor_add_one (div_nonneg ha hu.le)).symm
    _ ≤ ⌊b / u⌋₊ := Nat.floor_le_floor h1

/-- A set of cells `E ⊆ {0, …, M - 1}²` without a `t × t` grid (`t ≤ 3`) gives an open subset of
`[0, M u]³`, made of boxes `(i u, (i + 1) u) × (0, M u) × (j u, (j + 1) u)` for `(i, j) ∈ E`, that
avoids the stacked plus sign when the cell size `u` is at most `r` and at most `c`. -/
private theorem le_opxD_of_cells {t : ℕ} (ht : t ≤ 3) {r c u : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hu : 0 < u) (hur : u ≤ r) (huc : u ≤ c) {M : ℕ} {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 < M ∧ e.2 < M)
    (hfree : ∀ I J : Finset ℕ, I.card = t → J.card = t → ¬ I ×ˢ J ⊆ E) :
    E.card * u ^ 2 * (M * u) ≤ opxD 3 (M * u) {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧
      (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c} := by
  set N : ℝ := M * u with hN
  let lo : ℕ × ℕ → Fin 3 → ℝ := fun e => ![e.1 * u, 0, e.2 * u]
  let hi : ℕ × ℕ → Fin 3 → ℝ := fun e => ![(e.1 + 1) * u, N, (e.2 + 1) * u]
  let box : ℕ × ℕ → Set (Fin 3 → ℝ) := fun e => univ.pi fun k => Ioo (lo e k) (hi e k)
  set S := ⋃ e ∈ E, box e with hS_def
  have hboxopen : ∀ e, IsOpen (box e) := fun e => isOpen_set_pi finite_univ fun k _ => isOpen_Ioo
  have hfloor : ∀ e, ∀ v ∈ box e, ⌊v 0 / u⌋₊ = e.1 ∧ ⌊v 2 / u⌋₊ = e.2 ∧ 0 < v 0 ∧ 0 < v 2 := by
    intro e v hv
    have h0 := hv 0 (mem_univ _)
    have h2 := hv 2 (mem_univ _)
    simp only [lo, hi, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, mem_Ioo] at h0 h2
    have hf : ∀ (k : ℕ) (x : ℝ), k * u < x → x < (k + 1) * u → ⌊x / u⌋₊ = k := by
      intro k x h1 h2
      rw [Nat.floor_eq_iff (div_nonneg ((by positivity : (0 : ℝ) ≤ k * u).trans h1.le) hu.le),
        le_div_iff₀ hu, div_lt_iff₀ hu]
      exact ⟨h1.le, h2⟩
    exact ⟨hf _ _ h0.1 h0.2, hf _ _ h2.1 h2.2, (by positivity : (0 : ℝ) ≤ e.1 * u).trans_lt h0.1,
      (by positivity : (0 : ℝ) ≤ e.2 * u).trans_lt h2.1⟩
  have hSopen : IsOpen S := isOpen_biUnion fun e _ => hboxopen e
  have hSn : S ⊆ Icc 0 (fun _ => N) := by
    intro v hv
    obtain ⟨e, he, hv⟩ := mem_iUnion₂.1 hv
    have hM := hE e he
    have h1 : (e.1 : ℝ) + 1 ≤ M := by exact_mod_cast hM.1
    have h2 : (e.2 : ℝ) + 1 ≤ M := by exact_mod_cast hM.2
    refine ⟨fun k => ?_, fun k => ?_⟩ <;> have hk := hv k (mem_univ _) <;> fin_cases k <;>
      simp only [lo, hi, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, mem_Ioo, Pi.zero_apply] at hk ⊢
    · exact ((by positivity : (0 : ℝ) ≤ e.1 * u).trans hk.1.le)
    · exact hk.1.le
    · exact ((by positivity : (0 : ℝ) ≤ e.2 * u).trans hk.1.le)
    · exact hk.2.le.trans (by rw [hN]; gcongr)
    · exact hk.2.le
    · exact hk.2.le.trans (by rw [hN]; gcongr)
  have hdisj : (E : Set (ℕ × ℕ)).PairwiseDisjoint box := by
    intro e _ e' _ hee'
    refine disjoint_left.2 fun v hv hv' => hee' ?_
    obtain ⟨h1, h2, -, -⟩ := hfloor e v hv
    obtain ⟨h1', h2', -, -⟩ := hfloor e' v hv'
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')
  have hvol : volume S = E.card * (ENNReal.ofReal u * ENNReal.ofReal N * ENNReal.ofReal u) := by
    rw [hS_def, measure_biUnion_finset hdisj fun e _ => (hboxopen e).measurableSet]
    have : ∀ e, volume (box e) = ENNReal.ofReal u * ENNReal.ofReal N * ENNReal.ofReal u := by
      intro e
      simp only [box, Real.volume_pi_Ioo, Fin.prod_univ_three, lo, hi, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      congr 2 <;> ring_nf
    simp [this]
  have hfreeS : ¬ ContainsPatternD S {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧
      (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c} := by
    rintro ⟨f, hf, himg⟩
    let P : Fin t → Fin t → Fin 3 → ℝ := fun k l =>
      ![(((k : ℕ) : ℝ) - 1) * r, 0, (((l : ℕ) : ℝ) + 1) * c]
    have hP : ∀ k l : Fin t, P k l ∈ {v : Fin 3 → ℝ | |v 0| ≤ r ∧ |v 1| ≤ r ∧
        (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c} := by
      intro k l
      have hk : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
      have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
      refine ⟨?_, by simp [P, hr.le], Or.inr (by simp [P]), (l : ℕ) + 1, by omega,
        by omega, by simp [P]⟩
      simp only [P, Matrix.cons_val_zero]
      rw [abs_le]
      constructor <;> nlinarith
    have hcell : ∀ k l : Fin t, (⌊f 0 ((((k : ℕ) : ℝ) - 1) * r) / u⌋₊,
        ⌊f 2 ((((l : ℕ) : ℝ) + 1) * c) / u⌋₊) ∈ E ∧
        0 < f 0 ((((k : ℕ) : ℝ) - 1) * r) ∧ 0 < f 2 ((((l : ℕ) : ℝ) + 1) * c) := by
      intro k l
      obtain ⟨e, he, hv⟩ := mem_iUnion₂.1 (himg _ (hP k l))
      obtain ⟨h0, h2, hp0, hp2⟩ := hfloor e _ hv
      simp only [P, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at h0 h2 hp0 hp2
      refine ⟨?_, hp0, hp2⟩
      rw [h0, h2]
      exact he
    have hmonoX : StrictMono fun k : Fin t => ⌊f 0 ((((k : ℕ) : ℝ) - 1) * r) / u⌋₊ := by
      intro k k' hkk
      have hkk' : ((k : ℕ) : ℝ) + 1 ≤ (k' : ℕ) := by exact_mod_cast hkk
      have hlt : (((k : ℕ) : ℝ) - 1) * r < (((k' : ℕ) : ℝ) - 1) * r := by nlinarith
      have h := hf 0 (P k' k) (hP _ _) (P k k) (hP _ _) (by simpa [P] using hlt)
      simp only [P, Matrix.cons_val_zero] at h
      refine floor_lt_floor_of_add_le hu (hcell k k).2.1.le ?_
      nlinarith
    have hmonoZ : StrictMono fun l : Fin t => ⌊f 2 ((((l : ℕ) : ℝ) + 1) * c) / u⌋₊ := by
      intro l l' hll
      have hll' : ((l : ℕ) : ℝ) + 1 ≤ (l' : ℕ) := by exact_mod_cast hll
      have hlt : (((l : ℕ) : ℝ) + 1) * c < (((l' : ℕ) : ℝ) + 1) * c := by nlinarith
      have h := hf 2 (P l l') (hP _ _) (P l l) (hP _ _) (by simpa [P] using hlt)
      simp only [P, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
      refine floor_lt_floor_of_add_le hu (hcell l l).2.2.le ?_
      nlinarith
    classical
    refine hfree (Finset.univ.image fun k : Fin t => ⌊f 0 ((((k : ℕ) : ℝ) - 1) * r) / u⌋₊)
      (Finset.univ.image fun l : Fin t => ⌊f 2 ((((l : ℕ) : ℝ) + 1) * c) / u⌋₊)
      (by rw [Finset.card_image_of_injective _ hmonoX.injective, Finset.card_univ,
        Fintype.card_fin])
      (by rw [Finset.card_image_of_injective _ hmonoZ.injective, Finset.card_univ,
        Fintype.card_fin]) ?_
    rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_image, Finset.mem_univ, true_and] at hij
    obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := hij
    exact (hcell k l).1
  calc (E.card : ℝ) * u ^ 2 * N = volume.real S := by
        rw [Measure.real, hvol, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hu.le, ENNReal.toReal_ofReal (by positivity)]
        simp only [ENNReal.toReal_natCast]
        ring
    _ ≤ _ := opxD_add_lt.volume_le_opxD hSopen hSn hfreeS

/-- A relation on a finite type without `t × t` grids gives a set of cells of the same size,
inside `{0, …, |V| - 1}²`, without `t × t` grids. -/
private theorem exists_cells {V : Type*} [Fintype V] (R : V → V → Prop) [DecidableRel R] {t : ℕ}
    (hR : ∀ A B : Finset V, A.card = t → B.card = t → ¬ ∀ a ∈ A, ∀ b ∈ B, R a b) :
    ∃ E : Finset (ℕ × ℕ), (∀ e ∈ E, e.1 < Fintype.card V ∧ e.2 < Fintype.card V) ∧
      E.card = (Finset.univ.filter fun ab : V × V => R ab.1 ab.2).card ∧
      ∀ I J : Finset ℕ, I.card = t → J.card = t → ¬ I ×ˢ J ⊆ E := by
  classical
  let enc : V → ℕ := fun a => (Fintype.equivFin V a : ℕ)
  have henc : Function.Injective enc := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  let encp : V × V → ℕ × ℕ := fun ab => (enc ab.1, enc ab.2)
  have hencp : Function.Injective encp := fun x y h =>
    Prod.ext (henc (congrArg Prod.fst h)) (henc (congrArg Prod.snd h))
  refine ⟨(Finset.univ.filter fun ab : V × V => R ab.1 ab.2).image encp, ?_,
    Finset.card_image_of_injective _ hencp, ?_⟩
  · intro e he
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨(Fintype.equivFin V ab.1).2, (Fintype.equivFin V ab.2).2⟩
  · intro I J hI hJ hIJ
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hR ∅ ∅ rfl rfl (by simp)
    have hrange : ∀ {I J : Finset ℕ}, J.card = t → (∀ i ∈ I, ∀ j ∈ J, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp) → (Finset.univ.filter fun a => enc a ∈ I).image
        enc = I := by
      intro I J hJ hIJ
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hi
        obtain ⟨j, hj⟩ : J.Nonempty := by rw [← Finset.card_pos, hJ]; exact ht
        obtain ⟨ab, -, hab⟩ := Finset.mem_image.1 (hIJ i hi j hj)
        have hab1 : enc ab.1 = i := congrArg Prod.fst hab
        exact ⟨ab.1, by rw [hab1]; exact hi, hab1⟩
    have hIJ' : ∀ i ∈ I, ∀ j ∈ J, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp := fun i hi j hj =>
      hIJ (Finset.mem_product.2 ⟨hi, hj⟩)
    have hJI' : ∀ j ∈ J, ∀ i ∈ I, (i, j) ∈ (Finset.univ.filter
        fun ab : V × V => R ab.1 ab.2).image encp := fun j hj i hi => hIJ' i hi j hj
    have hA := hrange hJ hIJ'
    have hB : (Finset.univ.filter fun b => enc b ∈ J).image enc = J := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hb
      · intro hj
        obtain ⟨i, hi⟩ : I.Nonempty := by rw [← Finset.card_pos, hI]; exact ht
        obtain ⟨ab, -, hab⟩ := Finset.mem_image.1 (hJI' j hj i hi)
        have hab2 : enc ab.2 = j := congrArg Prod.snd hab
        exact ⟨ab.2, by rw [hab2]; exact hj, hab2⟩
    refine hR (Finset.univ.filter fun a => enc a ∈ I) (Finset.univ.filter fun b => enc b ∈ J)
      (by rw [← Finset.card_image_of_injective _ henc, hA, hI])
      (by rw [← Finset.card_image_of_injective _ henc, hB, hJ]) ?_
    intro a ha b hb
    obtain ⟨ab, hab, heq⟩ := Finset.mem_image.1
      (hIJ' _ (Finset.mem_filter.1 ha).2 _ (Finset.mem_filter.1 hb).2)
    have : ab = (a, b) := hencp heq
    subst this
    exact (Finset.mem_filter.1 hab).2

/-- Points and non-vertical lines of `𝔽_p²`: two points lie on at most one common line. -/
private theorem lines_free {F : Type*} [Field F] :
    ∀ A B : Finset (F × F), A.card = 2 → B.card = 2 →
      ¬ ∀ a ∈ A, ∀ b ∈ B, a.2 = b.1 * a.1 + b.2 := by
  classical
  intro A B hA hB h
  obtain ⟨a1, a2, ha, rfl⟩ := Finset.card_eq_two.1 hA
  obtain ⟨b1, b2, hb, rfl⟩ := Finset.card_eq_two.1 hB
  have h11 := h a1 (by simp) b1 (by simp)
  have h12 := h a1 (by simp) b2 (by simp)
  have h21 := h a2 (by simp) b1 (by simp)
  have h22 := h a2 (by simp) b2 (by simp)
  by_cases hm : b1.1 = b2.1
  · exact hb (Prod.ext hm (by linear_combination h12 - h11 - a1.1 * hm))
  · have : (b1.1 - b2.1) * (a1.1 - a2.1) = 0 := by linear_combination h12 - h11 - h22 + h21
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hm (sub_eq_zero.1 h0)
    · have hx : a1.1 = a2.1 := sub_eq_zero.1 h0
      exact ha (Prod.ext hx (by rw [h11, h21, hx]))

/-- The point-line incidence relation of `𝔽_p²` has `p³` incidences. -/
private theorem card_lines (p : ℕ) [Fact p.Prime] :
    p ^ 3 ≤ (Finset.univ.filter fun ab : (ZMod p × ZMod p) × (ZMod p × ZMod p) =>
      ab.1.2 = ab.2.1 * ab.1.1 + ab.2.2).card := by
  classical
  let φ : (ZMod p × ZMod p) × ZMod p → (ZMod p × ZMod p) × (ZMod p × ZMod p) :=
    fun bx => ((bx.2, bx.1.1 * bx.2 + bx.1.2), bx.1)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.2 hxy.1.1
  calc p ^ 3 = (Finset.univ : Finset ((ZMod p × ZMod p) × ZMod p)).card := by
        simp [ZMod.card]
        ring
    _ = (Finset.univ.image φ).card := (Finset.card_image_of_injective _ hφ).symm
    _ ≤ _ := Finset.card_le_card fun ab hab => by
        obtain ⟨bx, -, rfl⟩ := Finset.mem_image.1 hab
        simp [φ]

section Brown

variable {F : Type*} [Field F]

/-- The quadratic form `w₀ w₁ + w₂²` on `F³`, whose level sets are the spheres of Brown's
`K_{3,3}`-free graph. -/
private def brownQ (w : Fin 3 → F) : F := w 0 * w 1 + w 2 ^ 2

/-- The polar form of `brownQ`. -/
private def brownB (u w : Fin 3 → F) : F := u 0 * w 1 + u 1 * w 0 + 2 * (u 2 * w 2)

/-- The linear map with `brownB u w = brownM u ⬝ᵥ w`. -/
private def brownM (w : Fin 3 → F) : Fin 3 → F := ![w 1, w 0, 2 * w 2]

private theorem brownQ_sub (u w : Fin 3 → F) :
    brownQ (u - w) = brownQ u + brownQ w - brownB u w := by
  simp only [brownQ, brownB, Pi.sub_apply]
  ring

private theorem brownQ_sub_smul (v A : Fin 3 → F) (l : F) :
    brownQ (v - l • A) = brownQ v + l ^ 2 * brownQ A - l * brownB v A := by
  simp only [brownQ, brownB, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem brownQ_neg (w : Fin 3 → F) : brownQ (-w) = brownQ w := by
  simp only [brownQ, Pi.neg_apply]
  ring

private theorem brownB_eq_dotProduct (u w : Fin 3 → F) : brownB u w = brownM u ⬝ᵥ w := by
  simp only [brownB, brownM, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem brownB_sub_sub (a a' b b' : Fin 3 → F) :
    brownB (b' - b) (a' - a) =
      brownQ (b - a') + brownQ (b' - a) - brownQ (b - a) - brownQ (b' - a') := by
  simp only [brownB, brownQ, Pi.sub_apply]
  ring

/-- On the plane orthogonal to a nonzero isotropic vector, `brownQ` takes only square values. -/
private theorem isSquare_brownQ {u w : Fin 3 → F} (hw : w ≠ 0) (hQ : brownQ w = 0)
    (hB : brownB u w = 0) : IsSquare (brownQ u) := by
  simp only [brownQ, brownB] at hQ hB ⊢
  by_cases h0 : w 0 = 0
  · by_cases h1 : w 1 = 0
    · exfalso
      apply hw
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · simp only [h0, h1, zero_mul, zero_add, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true] at hQ
        exact hQ
    · refine ⟨(u 1 * w 2 - u 2 * w 1) / w 1, ?_⟩
      field_simp
      linear_combination (-(u 1) ^ 2) * hQ + (u 1 * w 1) * hB
  · refine ⟨(u 0 * w 2 - u 2 * w 0) / w 0, ?_⟩
    field_simp
    linear_combination (-(u 0) ^ 2) * hQ + (u 0 * w 0) * hB

/-- Three collinear points `v, v - A, v - l A` cannot all lie on the sphere `brownQ = r` with
`r` a nonsquare: such a sphere contains no line. -/
private theorem brown_collinear {r : F} (hr : ¬ IsSquare r) {v A : Fin 3 → F} {l : F}
    (hA : A ≠ 0) (hl0 : l ≠ 0) (hl1 : l ≠ 1) (h1 : brownQ v = r) (h2 : brownQ (v - A) = r)
    (h3 : brownQ (v - l • A) = r) : False := by
  rw [brownQ_sub] at h2
  rw [brownQ_sub_smul] at h3
  have hQA : brownQ A = brownB v A := by linear_combination h2 - h1
  have hQA0 : brownQ A = 0 := by
    have : l * (l - 1) * brownQ A = 0 := by linear_combination h3 - h1 - l * hQA
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hl0
      · exact absurd (sub_eq_zero.1 h) hl1
    · exact h
  exact hr (h1 ▸ isSquare_brownQ hA hQA0 (hQA ▸ hQA0))

/-- If `X × Y = 0` with `X ≠ 0`, then `Y` is a multiple of `X`. -/
private theorem exists_smul_of_cross_eq_zero {X Y : Fin 3 → F} (hX : X ≠ 0)
    (h : crossProduct X Y = 0) : ∃ l : F, Y = l • X := by
  rw [cross_apply] at h
  have h0 : X 1 * Y 2 - X 2 * Y 1 = 0 := by simpa using congrFun h 0
  have h1 : X 2 * Y 0 - X 0 * Y 2 = 0 := by simpa using congrFun h 1
  have h2 : X 0 * Y 1 - X 1 * Y 0 = 0 := by simpa using congrFun h 2
  by_cases hx0 : X 0 = 0
  · by_cases hx1 : X 1 = 0
    · have hx2 : X 2 ≠ 0 := fun hx2 => hX (by ext i; fin_cases i <;> simp [hx0, hx1, hx2])
      refine ⟨Y 2 / X 2, ?_⟩
      ext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Pi.smul_apply, smul_eq_mul] <;> field_simp
      · simp only [hx0, zero_mul, sub_zero, mul_eq_zero, hx2, false_or] at h1
        simp [h1, hx0]
      · simp only [hx1, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, hx2, false_or] at h0
        simp [h0, hx1]
    · refine ⟨Y 1 / X 1, ?_⟩
      ext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Pi.smul_apply, smul_eq_mul] <;> field_simp
      · simp only [hx0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, hx1, false_or] at h2
        simp [h2, hx0]
      · linear_combination h0
  · refine ⟨Y 0 / X 0, ?_⟩
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.smul_apply, smul_eq_mul] <;> field_simp
    · linear_combination h2
    · linear_combination -h1

/-- **Brown's construction.** Distinct points `a₁, a₂, a₃` and `b₁, b₂, b₃` of `F³` (with
`2 ≠ 0` in `F`) cannot satisfy `brownQ (b_j - a_i) = r` for all `i, j` when `r` is a
nonsquare. -/
private theorem brown_free (h2 : (2 : F) ≠ 0) {r : F} (hr : ¬ IsSquare r) :
    ∀ A B : Finset (Fin 3 → F), A.card = 3 → B.card = 3 →
      ¬ ∀ a ∈ A, ∀ b ∈ B, brownQ (b - a) = r := by
  classical
  intro A B hA hB h
  obtain ⟨a1, a2, a3, ha12, ha13, ha23, rfl⟩ := Finset.card_eq_three.1 hA
  obtain ⟨b1, b2, b3, hb12, hb13, hb23, rfl⟩ := Finset.card_eq_three.1 hB
  have h11 := h a1 (by simp) b1 (by simp)
  have h12 := h a1 (by simp) b2 (by simp)
  have h13 := h a1 (by simp) b3 (by simp)
  have h21 := h a2 (by simp) b1 (by simp)
  have h22 := h a2 (by simp) b2 (by simp)
  have h23 := h a2 (by simp) b3 (by simp)
  have h31 := h a3 (by simp) b1 (by simp)
  have h32 := h a3 (by simp) b2 (by simp)
  have h33 := h a3 (by simp) b3 (by simp)
  have hor : ∀ {a a' b b' : Fin 3 → F}, brownQ (b - a) = r → brownQ (b - a') = r →
      brownQ (b' - a) = r → brownQ (b' - a') = r → brownB (b' - b) (a' - a) = 0 := by
    intro a a' b b' e1 e2 e3 e4
    rw [brownB_sub_sub, e1, e2, e3, e4]
    ring
  have hA2 : a2 - a1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha12)
  have hA3 : a3 - a1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha13)
  have hB2 : b2 - b1 ≠ 0 := sub_ne_zero.2 (Ne.symm hb12)
  by_cases hC : crossProduct (a2 - a1) (a3 - a1) = 0
  · obtain ⟨l, hl⟩ := exists_smul_of_cross_eq_zero hA2 hC
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hA3 (by simpa using hl)
    have hl1 : l ≠ 1 := by
      rintro rfl
      exact ha23 (by simpa using hl.symm)
    refine brown_collinear hr hA2 hl0 hl1 h11 ?_ ?_
    · rw [show b1 - a1 - (a2 - a1) = b1 - a2 by abel]
      exact h21
    · rw [← hl, show b1 - a1 - (a3 - a1) = b1 - a3 by abel]
      exact h31
  · have hX : ∀ {b' : Fin 3 → F}, brownB (b' - b1) (a2 - a1) = 0 →
        brownB (b' - b1) (a3 - a1) = 0 →
        crossProduct (crossProduct (a2 - a1) (a3 - a1)) (brownM (b' - b1)) = 0 := by
      intro b' e2 e3
      rw [brownB_eq_dotProduct] at e2 e3
      rw [← cross_anticomm, cross_cross_eq_smul_sub_smul', dotProduct_comm (a2 - a1), e2, e3]
      simp
    obtain ⟨μ2, hμ2⟩ := exists_smul_of_cross_eq_zero hC
      (hX (hor h11 h21 h12 h22) (hor h11 h31 h12 h32))
    obtain ⟨μ3, hμ3⟩ := exists_smul_of_cross_eq_zero hC
      (hX (hor h11 h21 h13 h23) (hor h11 h31 h13 h33))
    have hM : ∀ w : Fin 3 → F, brownM w = 0 → w = 0 := by
      intro w hw
      have e0 := congrFun hw 0
      have e1 := congrFun hw 1
      have e2 := congrFun hw 2
      simp only [brownM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply, mul_eq_zero, h2, false_or] at e0 e1 e2
      ext i
      fin_cases i
      · exact e1
      · exact e0
      · exact e2
    have hμ2' : μ2 ≠ 0 := by
      rintro rfl
      exact hB2 (hM _ (by simpa using hμ2))
    set l := μ3 / μ2 with hl_def
    have hl : b3 - b1 = l • (b2 - b1) := by
      have : brownM (b3 - b1 - l • (b2 - b1)) = 0 := by
        have hlin : brownM (b3 - b1 - l • (b2 - b1)) =
            brownM (b3 - b1) - l • brownM (b2 - b1) := by
          ext i
          fin_cases i
          · simp [brownM]
          · simp [brownM]
          · simp [brownM]
            ring
        rw [hlin, hμ2, hμ3, smul_smul, hl_def, div_mul_cancel₀ _ hμ2', sub_self]
      exact sub_eq_zero.1 (hM _ this)
    have hl0 : l ≠ 0 := by
      rintro h0
      rw [h0, zero_smul, sub_eq_zero] at hl
      exact hb13 hl.symm
    have hl1 : l ≠ 1 := by
      rintro h1
      rw [h1, one_smul, sub_left_inj] at hl
      exact hb23 hl.symm
    refine brown_collinear hr hB2 hl0 hl1 (v := a1 - b1) ?_ ?_ ?_
    · rw [← brownQ_neg, neg_sub]
      exact h11
    · rw [show a1 - b1 - (b2 - b1) = -(b2 - a1) by abel, brownQ_neg]
      exact h12
    · rw [← hl, show a1 - b1 - (b3 - b1) = -(b3 - a1) by abel, brownQ_neg]
      exact h13

end Brown

/-- Brown's graph has at least `q³ (q - 1) q` edges: from every `a`, the points
`a + (x, (r - z²) / x, z)` with `x ≠ 0` lie on the sphere `brownQ (b - a) = r`. -/
private theorem card_brown {F : Type*} [Field F] [Fintype F] [DecidableEq F] (r : F) :
    Fintype.card F ^ 3 * ((Fintype.card F - 1) * Fintype.card F) ≤
      (Finset.univ.filter fun ab : (Fin 3 → F) × (Fin 3 → F) =>
        brownQ (ab.2 - ab.1) = r).card := by
  let φ : (Fin 3 → F) × F × F → (Fin 3 → F) × (Fin 3 → F) :=
    fun axz => (axz.1, axz.1 + ![axz.2.1, (r - axz.2.2 ^ 2) / axz.2.1, axz.2.2])
  have hφ : Function.Injective φ := by
    rintro ⟨a, x, z⟩ ⟨a', x', z'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, add_right_inj] at h0 h2
    rw [h0, h2]
  let D : Finset ((Fin 3 → F) × F × F) :=
    Finset.univ ×ˢ ((Finset.univ.filter fun x : F => x ≠ 0) ×ˢ Finset.univ)
  have hD : D.card = Fintype.card F ^ 3 * ((Fintype.card F - 1) * Fintype.card F) := by
    simp only [D, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [Finset.filter_ne' Finset.univ (0 : F), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  calc _ = D.card := hD.symm
    _ = (D.image φ).card := (Finset.card_image_of_injective _ hφ).symm
    _ ≤ _ := Finset.card_le_card fun ab hab => by
        obtain ⟨⟨a, x, z⟩, hxz, rfl⟩ := Finset.mem_image.1 hab
        have hx : x ≠ 0 := (Finset.mem_filter.1 (Finset.mem_product.1
          (Finset.mem_product.1 hxz).2).1).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ, add_sub_cancel_left]
        simp only [brownQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        field_simp
        ring

/-- The upper bound on `opx(n, Q_{P,t,c}, 3)` for the plus sign `P` of size `r`. -/
private theorem opxD_le {t : ℕ} (ht : 2 ≤ t) {r c n : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hn : 0 < n) :
    opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧ v 2 = i * c} ≤
      t * c * n ^ 2 + t * (4 * r) ^ (1 / t : ℝ) * n ^ (3 - 1 / t : ℝ) := by
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨S, ⟨hS, hSn, hfree⟩, rfl⟩
  exact volume_le_of_free ht hr hc hn hS hSn hfree

/-- The lower bound on `opx(n, Q_{P,2,c}, 3)`, from the point-line incidence graph of `𝔽_p²`. -/
private theorem opxD_two_ge {r c n : ℝ} (hr : 0 < r) (hc : 0 < c) (hn : min r c ≤ n) :
    Real.sqrt (min r c) / 4 * n ^ (5 / 2 : ℝ) ≤ opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧
      (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c} := by
  set κ := min r c with hκ_def
  have hκ : 0 < κ := lt_min hr hc
  have hn0 : 0 < n := hκ.trans_le hn
  set s := Real.sqrt (n / κ) with hs_def
  have hs1 : 1 ≤ s := by
    rw [hs_def, Real.one_le_sqrt]
    exact (one_le_div hκ).2 hn
  have hs2 : s ^ 2 = n / κ := Real.sq_sqrt (by positivity)
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈s⌉₊
    (Nat.ceil_pos.2 (by linarith)).ne'
  have := Fact.mk hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hps : s < p := (Nat.le_ceil s).trans_lt (by exact_mod_cast hmp)
  have hp4 : (p : ℝ) ≤ 4 * s := by
    have h1 : (p : ℝ) ≤ 2 * ⌈s⌉₊ := by exact_mod_cast hp2m
    have h2 := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
    linarith
  set u := n / (p : ℝ) ^ 2 with hu_def
  have hu : 0 < u := by positivity
  have huκ : u ≤ κ := by
    rw [hu_def, div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 ≤ (p : ℝ) ^ 2 := by gcongr
    rw [hs2, div_le_iff₀ hκ] at h1
    linarith
  obtain ⟨E, hE, hEcard, hEfree⟩ := exists_cells (V := ZMod p × ZMod p)
    (fun a b => a.2 = b.1 * a.1 + b.2) lines_free
  have hcardV : Fintype.card (ZMod p × ZMod p) = p ^ 2 := by simp [ZMod.card, sq]
  rw [hcardV] at hE
  have key := le_opxD_of_cells (t := 2) (by norm_num) hr hc hu (huκ.trans (min_le_left _ _))
    (huκ.trans (min_le_right _ _)) hE hEfree
  have hMu : ((p ^ 2 : ℕ) : ℝ) * u = n := by
    rw [hu_def]
    push_cast
    field_simp
  rw [hMu] at key
  have hE3 : (p : ℝ) ^ 3 ≤ E.card := by
    rw [hEcard]
    exact_mod_cast card_lines p
  refine le_trans ?_ key
  have hsn : s = Real.sqrt n / Real.sqrt κ := by rw [hs_def, Real.sqrt_div' _ hκ.le]
  have h52 : n ^ (5 / 2 : ℝ) = n ^ 2 * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]
    norm_num
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  calc Real.sqrt κ / 4 * n ^ (5 / 2 : ℝ) = n ^ 3 / (4 * s) := by
        rw [h52, hsn]
        field_simp
        rw [Real.sq_sqrt hn0.le]
    _ ≤ n ^ 3 / p := by gcongr
    _ = p ^ 3 * u ^ 2 * n := by
        rw [hu_def]
        field_simp
    _ ≤ E.card * u ^ 2 * n := by gcongr

/-- The lower bound on `opx(n, Q_{P,3,c}, 3)`, from Brown's unit-sphere graph of `𝔽_p³`. -/
private theorem opxD_three_ge {r c n : ℝ} (hr : 0 < r) (hc : 0 < c) (hn : 8 * min r c ≤ n) :
    min r c ^ (1 / 3 : ℝ) / 16 * n ^ (8 / 3 : ℝ) ≤ opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧
      (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c} := by
  set κ := min r c with hκ_def
  have hκ : 0 < κ := lt_min hr hc
  have hn0 : 0 < n := by linarith
  set s := (n / κ) ^ (1 / 3 : ℝ) with hs_def
  have hs3 : s ^ 3 = n / κ := by
    rw [hs_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hs0 : 0 ≤ s := by positivity
  have hs2 : 2 ≤ s := by
    have h8 : (8 : ℝ) ≤ n / κ := by rw [le_div_iff₀ hκ]; linarith
    have : (2 : ℝ) ^ 3 ≤ s ^ 3 := by rw [hs3]; norm_num; exact h8
    exact le_of_pow_le_pow_left₀ (by norm_num) hs0 this
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈s⌉₊
    (Nat.ceil_pos.2 (by linarith)).ne'
  have := Fact.mk hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hps : s < p := (Nat.le_ceil s).trans_lt (by exact_mod_cast hmp)
  have hp3 : 3 ≤ p := by
    have : (2 : ℝ) < p := by linarith
    exact_mod_cast this
  have hp4 : (p : ℝ) ≤ 4 * s := by
    have h1 : (p : ℝ) ≤ 2 * ⌈s⌉₊ := by exact_mod_cast hp2m
    have h2 := Nat.ceil_lt_add_one hs0
    linarith
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨ρ, hρ⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  classical
  obtain ⟨E, hE, hEcard, hEfree⟩ := exists_cells (V := Fin 3 → ZMod p)
    (fun a b => brownQ (b - a) = ρ) (brown_free h2 hρ)
  have hcardV : Fintype.card (Fin 3 → ZMod p) = p ^ 3 := by simp [ZMod.card]
  rw [hcardV] at hE
  set u := n / (p : ℝ) ^ 3 with hu_def
  have hu : 0 < u := by positivity
  have huκ : u ≤ κ := by
    rw [hu_def, div_le_iff₀ (by positivity)]
    have h1 : s ^ 3 ≤ (p : ℝ) ^ 3 := by gcongr
    rw [hs3, div_le_iff₀ hκ] at h1
    linarith
  have key := le_opxD_of_cells (t := 3) le_rfl hr hc hu (huκ.trans (min_le_left _ _))
    (huκ.trans (min_le_right _ _)) hE hEfree
  have hMu : ((p ^ 3 : ℕ) : ℝ) * u = n := by
    rw [hu_def]
    push_cast
    field_simp
  rw [hMu] at key
  have hEc : (p : ℝ) ^ 3 * (((p : ℝ) - 1) * p) ≤ E.card := by
    rw [hEcard]
    have h := card_brown (F := ZMod p) ρ
    rw [ZMod.card] at h
    calc (p : ℝ) ^ 3 * (((p : ℝ) - 1) * p) = ((p ^ 3 * ((p - 1) * p) : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hp.one_le]
          ring
      _ ≤ _ := by exact_mod_cast h
  refine le_trans ?_ key
  have hsn : s = n ^ (1 / 3 : ℝ) / κ ^ (1 / 3 : ℝ) := by
    rw [hs_def, Real.div_rpow hn0.le hκ.le]
  have h83 : n ^ (8 / 3 : ℝ) * n ^ (1 / 3 : ℝ) = n ^ 3 := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast]
    norm_num
  have hn13 : 0 < n ^ (1 / 3 : ℝ) := by positivity
  have hκ13 : 0 < κ ^ (1 / 3 : ℝ) := by positivity
  calc κ ^ (1 / 3 : ℝ) / 16 * n ^ (8 / 3 : ℝ) ≤ n ^ 3 / (2 * (4 * s)) := by
        rw [hsn, ← h83]
        field_simp
        nlinarith [pow_pos hn0 1]
    _ ≤ n ^ 3 / (2 * p) := by gcongr
    _ ≤ ((p : ℝ) - 1) / p ^ 2 * n ^ 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        have h := mul_nonneg (mul_nonneg (pow_pos hn0 3).le hp0.le) (by linarith : (0 : ℝ) ≤ p - 2)
        nlinarith [h]
    _ = p ^ 3 * (((p : ℝ) - 1) * p) * u ^ 2 * n := by
        rw [hu_def]
        field_simp
    _ ≤ E.card * u ^ 2 * n := by gcongr

end opxD_plus_stack_isTheta

open opxD_plus_stack_isTheta in
/-- **Stacked plus signs in three dimensions.** Let $r > 0$ and $c > 0$, let
$P = \{(x, y) \in \mathbb{R}^2 : |x| \le r,\ |y| \le r,\ x = 0 \text{ or } y = 0\}$ be the plus
sign of size $r$, and for $t \in \{2, 3\}$ let
$Q_{P,t,c} = \{(x, y, ic) : (x, y) \in P,\ i \in \{1, \dots, t\}\} \subseteq \mathbb{R}^3$. Then,
as the real number $n$ tends to infinity, $\mathrm{opx}(n, Q_{P,2,c}, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, Q_{P,3,c}, 3) = \Theta(n^{8/3})$.

The paper's size parameter $d$ is renamed $r$, and $r > 0$ is added: for $r = 0$, $Q_{P,2,c}$ is
two points on a vertical line and $\mathrm{opx}(n, Q_{P,2,c}, 3) \le c n^2$.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.19
(`integers-2024-A1-cor-5-19`). -/
public theorem opxD_plus_stack_isTheta {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (5 / 2 : ℝ)) ∧
      (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) =Θ[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ)) := by
  have hκ : 0 < min r c := lt_min hr hc
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine Asymptotics.IsBigO.of_bound (2 * c + 2 * (4 * r) ^ (1 / 2 : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by linarith
    rw [Real.norm_of_nonneg (opxD_nonneg _ _ _), Real.norm_of_nonneg (by positivity)]
    have h := opxD_le (t := 2) le_rfl hr hc hn0
    simp only [Nat.cast_ofNat] at h
    rw [show (3 : ℝ) - 1 / 2 = 5 / 2 by norm_num] at h
    have h2 : n ^ 2 ≤ n ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * c)]
  · refine Asymptotics.IsBigO.of_bound (4 / Real.sqrt (min r c)) ?_
    filter_upwards [Filter.eventually_ge_atTop (min r c)] with n hn
    have hn0 : 0 < n := hκ.trans_le hn
    have h := opxD_two_ge hr hc hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (opxD_nonneg _ _ _)]
    have hsq : 0 < Real.sqrt (min r c) := Real.sqrt_pos.2 hκ
    rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
    nlinarith
  · refine Asymptotics.IsBigO.of_bound (3 * c + 3 * (4 * r) ^ (1 / 3 : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by linarith
    rw [Real.norm_of_nonneg (opxD_nonneg _ _ _), Real.norm_of_nonneg (by positivity)]
    have h := opxD_le (t := 3) (by norm_num) hr hc hn0
    simp only [Nat.cast_ofNat] at h
    rw [show (3 : ℝ) - 1 / 3 = 8 / 3 by norm_num] at h
    have h2 : n ^ 2 ≤ n ^ (8 / 3 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 * c)]
  · refine Asymptotics.IsBigO.of_bound (16 / min r c ^ (1 / 3 : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop (8 * min r c)] with n hn
    have hn0 : 0 < n := by linarith
    have h := opxD_three_ge hr hc hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (opxD_nonneg _ _ _)]
    have hκ3 : 0 < min r c ^ (1 / 3 : ℝ) := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ3]
    nlinarith

end

end MetaMathlibExt
