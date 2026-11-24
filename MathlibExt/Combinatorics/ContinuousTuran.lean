/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Continuous Turán numbers in finite dimensions

Translating a planar pattern preserves its continuous Turán number.
The volume gained by enlarging the ambient cube bounds the increase in the supremum of volumes
of open sets avoiding a fixed pattern.
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

end

end MetaMathlibExt
