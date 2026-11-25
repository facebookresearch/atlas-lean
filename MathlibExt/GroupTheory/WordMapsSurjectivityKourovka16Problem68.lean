/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A non-surjective word map on the real projective special linear group

An explicit word has positive trace on all lifts to `SL(2, ℝ)`. Its projective word map
therefore misses the class of a trace-zero matrix, answering Kourovka Problem 16.68(a).

Let `a` be the first input and `b` its conjugate by the second. Write `x = (tr a)²`,
`s = tr (a * b)`, and `r = tr (a * b⁻¹) = x - s`. The trace of the word factors as
`(1 + x * (s - 2) * (2 - r))² + r - 1`. If `r < 2`, the commutator trace bound for
elliptic real matrices forces `4 ≤ x`, so `s - 2 ≥ 2 - r`. This gives positivity in the
only case where the square alone does not suffice.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted

/-- **Word map.** For a group $G$ and an element $w$ of the free group $F_2$ on two generators
$x_0, x_1$, the word map of $w$ is the map $G \times G \to G$ sending $(x, y)$ to $w(x, y)$, the
image of $w$ under the group homomorphism $F_2 \to G$ with $x_0 \mapsto x$ and $x_1 \mapsto y$. -/
def wordMap (G : Type*) [Group G] (w : FreeGroup (Fin 2)) (xy : G × G) : G :=
  FreeGroup.lift ![xy.1, xy.2] w

/-- **Surjectivity of word maps on $\mathrm{PSL}(2, \mathbb{R})$ (Kourovka 16.68(a)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{PSL}(2, \mathbb{R}) \times \mathrm{PSL}(2, \mathbb{R}) \to \mathrm{PSL}(2, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def psl2RealWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) w)

/-- **Surjectivity of word maps on $\mathrm{PSL}(2, \mathbb{C})$ (Kourovka 16.68(b)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{PSL}(2, \mathbb{C}) \times \mathrm{PSL}(2, \mathbb{C}) \to \mathrm{PSL}(2, \mathbb{C})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def psl2ComplexWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) w)

/-- **Surjectivity of word maps on $\mathrm{SO}(3, \mathbb{R})$ (Kourovka 16.68(c)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{SO}(3, \mathbb{R}) \times \mathrm{SO}(3, \mathbb{R}) \to \mathrm{SO}(3, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def so3WordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.specialOrthogonalGroup (Fin 3) ℝ) w)

open Matrix
open scoped MatrixGroups

private abbrev tr (a : SL(2, ℝ)) := a.val.trace

private theorem tr_comm (a b : SL(2, ℝ)) : tr (a * b) = tr (b * a) :=
  trace_mul_comm _ _

private theorem skein (a b : SL(2, ℝ)) : tr (a * b⁻¹) = tr a * tr b - tr (a * b) := by
  have h : b.val + (b⁻¹).val = tr b • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [SpecialLinearGroup.coe_inv, adjugate_fin_two, tr, trace_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  have e := congrArg (fun m => (a.val * m).trace) h
  simp only [Matrix.mul_add, trace_add, Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul] at e
  change tr (a * b) + tr (a * b⁻¹) = tr b * tr a at e
  linarith

private abbrev TraceCoords := ℝ × ℝ × ℝ × ℝ

-- Appending a letter acts linearly on these four traces by the skein identity.
private def coords (a b p : SL(2, ℝ)) : TraceCoords :=
  (tr p, tr (p * a), tr (p * b), tr (p * a * b))

private def stepA (z : ℝ) (v : TraceCoords) : TraceCoords :=
  let (t, x, y, s) := v
  (x, z * x - t, s, z * s - y)

private def stepB (z s : ℝ) (v : TraceCoords) : TraceCoords :=
  let (t, x, y, u) := v
  (y, (s - z ^ 2) * t + z * (x + y) - u, z * y - t, s * y + x - z * t)

private theorem coords_a (a b p : SL(2, ℝ)) :
    coords a b (p * a) = stepA (tr a) (coords a b p) := by
  have h := skein (p * a) a
  have k := skein (b * p * a) a
  simp only [mul_inv_cancel_right] at h k
  rw [mul_assoc b p a, tr_comm b (p * a), mul_assoc b (p * a) a,
    tr_comm b (p * a * a), tr_comm b p] at k
  unfold coords stepA
  congr 1
  congr 1
  · linarith
  · congr 1
    linarith

private theorem coords_b (a b p : SL(2, ℝ)) (hz : tr b = tr a) :
    coords a b (p * b) = stepB (tr a) (tr (a * b)) (coords a b p) := by
  have h := skein (p * b) b
  have k := skein (p * b) (a * b)
  have u := skein p (b * a)
  have v := skein (p * a⁻¹) b
  have w := skein (b * p) a
  have j := skein p a
  rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right, j, ← mul_assoc] at k
  rw [_root_.mul_inv_rev, ← mul_assoc, v, j, tr_comm b a, ← mul_assoc] at u
  rw [← tr_comm b (p * a⁻¹), ← mul_assoc, w, tr_comm b p, mul_assoc b p a,
    tr_comm b (p * a)] at u
  simp only [mul_inv_cancel_right, hz] at *
  unfold coords stepB
  congr 1
  congr 1
  · linarith
  · congr 1
    · linarith
    · linarith

private def backA (z : ℝ) (v : TraceCoords) : TraceCoords :=
  let (t, x, y, u) := v
  (z * t - x, t, z * y - u, y)

private def backB (z s : ℝ) (v : TraceCoords) : TraceCoords :=
  let (t, x, y, u) := v
  (z * t - y, (z ^ 2 - s) * t - z * y + u, t, z * u - s * y - x + z * t)

private theorem coords_inv_a (a b p : SL(2, ℝ)) :
    coords a b (p * a⁻¹) = backA (tr a) (coords a b p) := by
  have h := coords_a a b (p * a⁻¹)
  rw [inv_mul_cancel_right] at h
  rw [h]
  generalize coords a b (p * a⁻¹) = v
  obtain ⟨t, x, y, u⟩ := v
  simp [backA, stepA]

private theorem coords_inv_b (a b p : SL(2, ℝ)) (hz : tr b = tr a) :
    coords a b (p * b⁻¹) = backB (tr a) (tr (a * b)) (coords a b p) := by
  have h := coords_b a b (p * b⁻¹) hz
  rw [inv_mul_cancel_right] at h
  rw [h]
  generalize coords a b (p * b⁻¹) = v
  obtain ⟨t, x, y, u⟩ := v
  simp only [backB, stepB, Prod.mk.injEq, true_and]
  exact ⟨by ring, by ring, by ring⟩

-- Lowercase letters denote the two matrices and capital letters their inverses.
-- The word below reads AABBaaBAbaab.
private def letters {G : Type*} [Group G] (a b : G) : G :=
  a⁻¹ * a⁻¹ * b⁻¹ * b⁻¹ * a * a * b⁻¹ * a⁻¹ * b * a * a * b

private theorem trace_letters (a b : SL(2, ℝ)) (hz : tr b = tr a) :
    let x := (tr a) ^ 2
    let s := tr (a * b)
    let r := x - s
    tr (letters a b) = (1 + x * (s - 2) * (2 - r)) ^ 2 + r - 1 := by
  dsimp only
  change (coords a b (letters a b)).1 = _
  unfold letters
  nth_rw 1 [← one_mul a⁻¹]
  simp only [coords_a, coords_b a b _ hz, coords_inv_a, coords_inv_b a b _ hz]
  have h : coords a b 1 = (2, tr a, tr a, tr (a * b)) := by
    simp [coords, tr, one_mul, ← hz]
  rw [h]
  dsimp only [stepA, stepB, backA, backB]
  ring

-- An elliptic real matrix has commutator trace at least two. In the identity below
-- u and v are the entries in the first row of the additive commutator.
private theorem elliptic_comm (a y : SL(2, ℝ)) (ht : (tr a) ^ 2 < 4) :
    2 ≤ tr (a * y * a⁻¹ * y⁻¹) := by
  induction a using SpecialLinearGroup.fin_two_induction with | h a b c d ha =>
  induction y using SpecialLinearGroup.fin_two_induction with | h e f g h hy =>
  replace ht : (a + d) ^ 2 < 4 := by simpa [tr, trace_fin_two, SpecialLinearGroup.mk] using ht
  let u := b * g - f * c
  let v := (a - d) * f + b * (h - e)
  set r := tr _
  have hid : 4 * b ^ 2 * (r - 2) =
      (2 * b * u - (a - d) * v) ^ 2 + (4 - (a + d) ^ 2) * v ^ 2 := by
    dsimp [r, tr, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv, u, v]
    simp [adjugate_fin_two, trace_fin_two]
    linear_combination
      (8 * b ^ 2 * (e * h - f * g) + 4 * ((a - d) * f + b * (h - e)) ^ 2) * ha + 8 * b ^ 2 * hy
  have hb : b ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg (a - d)]
  have hpos : 0 < 4 * b ^ 2 := by positivity
  have hright : 0 ≤ (2 * b * u - (a - d) * v) ^ 2 + (4 - (a + d) ^ 2) * v ^ 2 := by
    have := sub_nonneg.mpr ht.le
    positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp (hid ▸ hright))

private def witness {G : Type*} [Group G] (a y : G) : G :=
  letters a (y * a * y⁻¹)

private theorem trace_witness_pos (a y : SL(2, ℝ)) : 0 < tr (witness a y) := by
  let b := y * a * y⁻¹
  have hz : tr b = tr a := by
    dsimp only [b]
    rw [tr_comm, inv_mul_cancel_left]
  let x := (tr a) ^ 2
  let s := tr (a * b)
  let r := x - s
  have hr : r = tr (a * y * a⁻¹ * y⁻¹) := by
    calc
      r = tr (a * b⁻¹) := by rw [skein, hz]; dsimp [r, x, s]; ring
      _ = _ := by congr 1; dsimp [b]; group
  change 0 < tr (letters a b)
  rw [trace_letters a b hz]
  change 0 < (1 + x * (s - 2) * (2 - r)) ^ 2 + r - 1
  by_cases h : 2 ≤ r
  · linarith [sq_nonneg (1 + x * (s - 2) * (2 - r))]
  have hx : 4 ≤ x := by
    by_contra! hx
    exact h (hr ▸ elliptic_comm a y hx)
  have hs : 2 - r ≤ s - 2 := by dsimp [r]; linarith
  have hd := sub_pos.mpr (lt_of_not_ge h)
  have hp : (2 - r) ^ 2 ≤ x * (s - 2) * (2 - r) := by
    calc
      (2 - r) ^ 2 = 1 * (2 - r) * (2 - r) := by ring
      _ ≤ _ := by gcongr; linarith
  nlinarith only [hp, sq_nonneg (x * (s - 2) * (2 - r)), sq_nonneg ((2 - r) - 1 / 4)]

private theorem trace_zero_of_mk_eq (m j : SL(2, ℝ)) (hj : tr j = 0)
    (h : (m : PSL(2, ℝ)) = j) : tr m = 0 := by
  obtain ⟨c, _, hc⟩ := SpecialLinearGroup.mem_center_iff.mp (QuotientGroup.eq_iff_div_mem.mp h)
  have heq : m.val = (m / j).val * j.val :=
    congrArg Subtype.val (div_mul_cancel m j).symm
  rw [← hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at heq
  change m.val.trace = 0
  rw [heq, trace_smul, show j.val.trace = 0 from hj, smul_zero]

/--
**Some nontrivial word map on $\mathrm{PSL}(2, \mathbb{R})$ is not surjective (Kourovka 16.68(a)).**
There is a nontrivial element $w$ of the free group $F_2$ on two generators whose word map
$\mathrm{PSL}(2, \mathbb{R}) \times \mathrm{PSL}(2, \mathbb{R}) \to \mathrm{PSL}(2, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is not surjective. That is, Mycielski's question has a negative answer
for $\mathrm{PSL}(2, \mathbb{R})$.

Nilradical (Theorem 2) gives an explicit nontrivial word $W$ (cyclically reduced length 44) with
$\operatorname{tr} W(A, B) > 7/4$ for all $A, B \in \mathrm{SL}(2, \mathbb{R})$; a nonidentity
involution of $\mathrm{PSL}(2, \mathbb{R})$ lifts to a matrix of trace $0$, so the word map of
$W$ misses it. The Kourovka Notebook (21st issue) records the negative answer for
$\mathrm{PSL}(2, \mathbb{R})$ (AI solution confirmed by A. Thom).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski); resolution:
Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September 2026); A.
Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, Nilradical,
Theorem 1 (every w ≠ 1 in F_2 induces a surjective map PSL_2(K)² → PSL_2(K) for K algebraically
closed of characteristic 0) and Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈
SL_2(ℝ)); Thom, Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u,
v ∈ U(n)), for SO(3, ℝ); the Kourovka Notebook (21st issue) marks 16.68 solved (AI solution
confirmed by A. Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
theorem psl2RealWordMapsSurjective_refuted : ¬ psl2RealWordMapsSurjective := by
  let w := witness (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1)
  have hw : w ≠ 1 := by decide
  let j : SL(2, ℝ) := .mk !![0, -1; 1, 0] (by norm_num [Matrix.det_fin_two])
  intro h
  obtain ⟨⟨u, v⟩, huv⟩ := h w hw (j : PSL(2, ℝ))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  let q := QuotientGroup.mk' (Subgroup.center (SL(2, ℝ)))
  have hq : q (witness a y) = (j : PSL(2, ℝ)) := by
    change wordMap _ w (q a, q y) = _ at huv
    simpa [wordMap, w, witness, letters] using huv
  exact (trace_witness_pos a y).ne' (trace_zero_of_mk_eq _ j (by simp [j, tr, trace_fin_two]) hq)

end MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted
