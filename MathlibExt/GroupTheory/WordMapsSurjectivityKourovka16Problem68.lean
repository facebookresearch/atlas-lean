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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Non-surjective word maps on the real projective special linear group and the rotation group

An explicit word has positive trace on all lifts to `SL(2, ℝ)`. Its projective word map
therefore misses the class of a trace-zero matrix, answering Kourovka Problem 16.68(a).

Let `a` be the first input and `b` its conjugate by the second. Write `x = (tr a)²`,
`s = tr (a * b)`, and `r = tr (a * b⁻¹) = x - s`. The trace of the word factors as
`(1 + x * (s - 2) * (2 - r))² + r - 1`. If `r < 2`, the commutator trace bound for
elliptic real matrices forces `4 ≤ x`, so `s - 2 ≥ 2 - r`. This gives positivity in the
only case where the square alone does not suffice.

For `SO(3, ℝ)`, we use Thom's commutator estimate in the operator norm. A finite cover
gives a uniform bound on the first positive power of a rotation within distance `1 / 4`
of the identity. Iterated commutators give a nontrivial word with uniformly small image,
which therefore misses a half-turn, answering Kourovka Problem 16.68(c).
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

/-! ### Small word maps on the rotation group -/

open scoped commutatorElement Matrix.Norms.L2Operator

private abbrev Word := FreeGroup (Fin 2)
private abbrev SO := specialOrthogonalGroup (Fin 3) ℝ
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

-- Record the first and last generators, ignoring the signs of their letters.
private def Ends (w : Word) (i j : Fin 2) : Prop :=
  w.toWord.head?.map Prod.fst = some i ∧ w.toWord.getLast?.map Prod.fst = some j

private theorem Ends.ne_one {w : Word} {i j : Fin 2} (h : Ends w i j) : w ≠ 1 := by
  rintro rfl
  simp [Ends] at h

private theorem Ends.inv {w : Word} {i j : Fin 2} (h : Ends w i j) : Ends w⁻¹ j i := by
  simpa [Ends, FreeGroup.invRev, Option.map_map, Function.comp_def] using h.symm

private theorem Ends.mul {u v : Word} {i j k l : Fin 2}
    (hu : Ends u i j) (hv : Ends v k l) (hjk : j ≠ k) : Ends (u * v) i l := by
  have hr : FreeGroup.IsReduced (u.toWord ++ v.toWord) := by
    apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
    intro a ha b hb hab
    change u.toWord.getLast? = some a at ha
    change v.toWord.head? = some b at hb
    have h₁ := hu.2
    have h₂ := hv.1
    rw [ha] at h₁
    rw [hb] at h₂
    exact (hjk ((Option.some.inj h₁).symm.trans (hab.trans (Option.some.inj h₂)))).elim
  have h₁ := mt FreeGroup.toWord_eq_nil_iff.mp hu.ne_one
  have h₂ := mt FreeGroup.toWord_eq_nil_iff.mp hv.ne_one
  simpa only [Ends, FreeGroup.toWord_mul, hr.reduce_eq, List.head?_append_of_ne_nil _ h₁,
    List.getLast?_append_of_ne_nil _ h₂] using And.intro hu.1 hv.2

private theorem ends_pow (i : Fin 2) (n : ℕ) : Ends (FreeGroup.of i ^ (n + 1)) i i := by
  simp only [Ends, FreeGroup.toWord_of_pow, ← List.head?_reverse, List.reverse_replicate]
  simp [List.replicate_succ]

-- Conjugate the commutator so that the next step can again join separated reduced words.
private def joinWords (u v : Word) : Word :=
  let x := FreeGroup.of (0 : Fin 2)
  let y := FreeGroup.of (1 : Fin 2)
  (x * y) * ⁅u, y * v * y⁻¹⁆ * (x * y)⁻¹

private theorem ends_join {u v : Word} (hu : Ends u 0 0) (hv : Ends v 0 0) :
    Ends (joinWords u v) 0 0 := by
  let x := FreeGroup.of (0 : Fin 2)
  let y := FreeGroup.of (1 : Fin 2)
  have hx : Ends x 0 0 := by simp [Ends, x]
  have hy : Ends y 1 1 := by simp [Ends, y]
  have hy₂ : Ends (y ^ 2) 1 1 := ends_pow 1 1
  have h : joinWords u v =
      x * y * u * y * v * y⁻¹ * u⁻¹ * y * v⁻¹ * (y ^ 2)⁻¹ * x⁻¹ := by
    dsimp [joinWords, x, y, commutatorElement_def]
    group
  rw [h]
  -- Consecutive factors in the expanded product meet at distinct generators.
  repeat' first | apply Ends.mul | assumption | apply Ends.inv | decide

private noncomputable def displacement (a : SO) : ℝ := ‖a.val - 1‖

private lemma orthogonal_unitary (a : SO) : a.val ∈ unitary Mat := a.prop.1

private theorem displacement_le_two (a : SO) : displacement a ≤ 2 := by
  have h := norm_sub_le a.val (1 : Mat)
  simpa [displacement, CStarRing.norm_of_mem_unitary (orthogonal_unitary a), one_add_one_eq_two]
    using h

private theorem displacement_conj (a b : SO) : displacement (a * b * a⁻¹) = displacement b := by
  have h : (a * b * a⁻¹).val - 1 = a.val * (b.val - 1) * a⁻¹.val := by
    have he : a.val * a⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel a)
    rw [mul_sub, mul_one, sub_mul, he]
    rfl
  rw [displacement, h, CStarRing.norm_mul_mem_unitary _ (orthogonal_unitary _),
    CStarRing.norm_mem_unitary_mul _ (orthogonal_unitary _), displacement]

private theorem displacement_comm (a b : SO) :
    displacement ⁅a, b⁆ ≤ 2 * displacement a * displacement b := by
  have h : (⁅a, b⁆.val - 1) * (b * a).val = a.val * b.val - b.val * a.val := by
    rw [sub_mul, one_mul, ← Submonoid.coe_mul]
    congr 1
    change (⁅a, b⁆ * (b * a)).val = (a * b).val
    apply congrArg Subtype.val
    rw [commutatorElement_def]
    group
  rw [displacement, ← CStarRing.norm_mul_mem_unitary _ (orthogonal_unitary (b * a)), h]
  have e : a.val * b.val - b.val * a.val =
      (a.val - 1) * (b.val - 1) - (b.val - 1) * (a.val - 1) := by noncomm_ring
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans ?_)
  dsimp only [displacement]
  linarith only [mul_comm ‖a.val - 1‖ ‖b.val - 1‖]

private theorem displacement_join (f : Word →* SO) (u v : Word) :
    displacement (f (joinWords u v)) ≤ 2 * displacement (f u) * displacement (f v) := by
  let y := f (FreeGroup.of 1)
  have h := displacement_comm (f u) (y * f v * y⁻¹)
  rw [displacement_conj] at h
  simpa only [joinWords, map_mul, map_inv, map_commutatorElement, displacement_conj] using h

-- A finite cover of the unit ball bounds the number of separated powers of any rotation.
private theorem exists_small_power : ∃ N : ℕ, ∀ a : SO, ∃ k < N,
    displacement (a ^ (k + 1)) ≤ 1 / 4 := by
  classical
  let : ProperSpace Mat := FiniteDimensional.proper ℝ Mat
  obtain ⟨t, _, ht, hcover⟩ := (isCompact_closedBall (0 : Mat) 1).finite_cover_balls
    (show (0 : ℝ) < 1 / 8 by norm_num)
  let := ht.fintype
  let N := Fintype.card t
  refine ⟨N, fun a => ?_⟩
  have h (i : Fin (N + 1)) : ∃ c : t, dist (a ^ (i : ℕ)).val c.val < 1 / 8 := by
    have hball : (a ^ (i : ℕ)).val ∈ Metric.closedBall (0 : Mat) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary
        (orthogonal_unitary _)]
    obtain ⟨c, hc, hm⟩ := Set.mem_iUnion₂.mp (hcover hball)
    exact ⟨⟨c, hc⟩, hm⟩
  choose c hc using h
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by simp [N])
  wlog hle : i < j generalizing i j
  · exact this j i hij.symm he.symm (lt_of_le_of_ne (le_of_not_gt hle) hij.symm)
  have hd := dist_triangle (a ^ (j : ℕ)).val (c i).val (a ^ (i : ℕ)).val
  rw [dist_comm (c i).val] at hd
  have hj := hc j
  rw [← he] at hj
  have hdist : ‖(a ^ (j : ℕ)).val - (a ^ (i : ℕ)).val‖ ≤ 1 / 4 := by
    rw [← dist_eq_norm]
    linarith [hc i]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (show (i : ℕ) < j from hle)
  refine ⟨k, by omega, ?_⟩
  rw [displacement, ← CStarRing.norm_mul_mem_unitary _ (orthogonal_unitary (a ^ (i : ℕ))),
    sub_mul, one_mul, ← Submonoid.coe_mul, ← pow_add]
  rwa [show k + 1 + (i : ℕ) = j by omega]

-- Arbitrarily small word maps on the rotations satisfying a given condition.
private def SmallOn (P : SO → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ w : Word, Ends w 0 0 ∧
    ∀ f : Word →* SO, P (f (FreeGroup.of 0)) → displacement (f w) ≤ ε

-- Once a power is small, taking a commutator with a conjugate of it halves displacement.
private theorem smallOn_power (k : ℕ) :
    SmallOn (fun a => displacement (a ^ (k + 1)) ≤ 1 / 4) := by
  let u : Word := FreeGroup.of 0 ^ (k + 1)
  have hu : Ends u 0 0 := ends_pow 0 k
  have shrink (m : ℕ) : ∃ w : Word, Ends w 0 0 ∧ ∀ f : Word →* SO,
      displacement (f u) ≤ 1 / 4 → displacement (f w) ≤ (1 / 2 : ℝ) ^ m := by
    induction m with
    | zero => exact ⟨u, hu, fun _ hf => by simpa using hf.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)⟩
    | succ m ih =>
      obtain ⟨w, hw, h⟩ := ih
      refine ⟨joinWords w u, ends_join hw hu, fun f hf => (displacement_join f w u).trans ?_⟩
      calc
        _ ≤ 2 * (1 / 2 : ℝ) ^ m * (1 / 4) := by
          gcongr <;> first | exact norm_nonneg _ | exact h f hf
        _ = _ := by rw [pow_succ]; ring
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨w, hw, h⟩ := shrink m
  exact ⟨w, hw, fun f hf => (h f (by simpa [u] using hf)).trans hm.le⟩

private theorem smallOn_or {P Q : SO → Prop} (hP : SmallOn P) (hQ : SmallOn Q) :
    SmallOn (fun a => P a ∨ Q a) := by
  intro ε hε
  obtain ⟨u, hu, h₁⟩ := hP (ε / 4) (by positivity)
  obtain ⟨v, hv, h₂⟩ := hQ (ε / 4) (by positivity)
  refine ⟨joinWords u v, ends_join hu hv, fun f h => (displacement_join f u v).trans ?_⟩
  have hn (a : SO) : 0 ≤ displacement a := norm_nonneg _
  rcases h with h | h
  · calc
      _ ≤ 2 * (ε / 4) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (h₁ f h) (by norm_num))
          (displacement_le_two _) (hn _) (by positivity)
      _ = ε := by ring
  · calc
      _ ≤ 2 * 2 * (ε / 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (displacement_le_two _) (by norm_num))
          (h₂ f h) (hn _) (by norm_num)
      _ = ε := by ring

-- Combine the first N power conditions into a single word.
private theorem smallOn_powers (N : ℕ) :
    SmallOn (fun a => ∃ k < N, displacement (a ^ (k + 1)) ≤ 1 / 4) := by
  induction N with
  | zero =>
    exact fun _ _ => ⟨_, ends_pow 0 0, by simp⟩
  | succ N ih =>
    simpa only [Nat.lt_succ_iff, le_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left]
      using smallOn_or ih (smallOn_power N)

private theorem half_turn : ∃ a : SO, 0 < displacement a := by
  let d : Fin 3 → ℝ := ![-1, -1, 1]
  have h : diagonal d ∈ specialOrthogonalGroup (Fin 3) ℝ := by
    rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, diagonal_transpose,
      diagonal_mul_diagonal, diagonal_eq_one, det_diagonal, Fin.prod_univ_three]
    constructor
    · funext i
      fin_cases i <;> norm_num [d]
    · norm_num [d]
  refine ⟨⟨_, h⟩, norm_pos_iff.mpr (sub_ne_zero.mpr ?_)⟩
  intro he
  have he₀ := congrArg (fun m : Mat => m 0 0) he
  norm_num [d] at he₀

/--
**Some nontrivial word map on $\mathrm{SO}(3, \mathbb{R})$ is not surjective (Kourovka 16.68(c)).**
There is a nontrivial element $w$ of the free group $F_2$ on two generators whose word map
$\mathrm{SO}(3, \mathbb{R}) \times \mathrm{SO}(3, \mathbb{R}) \to \mathrm{SO}(3, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is not surjective. That is, Mycielski's question has a negative answer
for $\mathrm{SO}(3, \mathbb{R})$.

The Kourovka Notebook (21st issue) answers 16.68 negatively for $\mathrm{SO}(3, \mathbb{R})$,
noting that this follows from Thom (2013), whose Corollary 1.2 gives, for every
$\varepsilon > 0$, a nontrivial word $w$ with $\|1 - w(u, v)\| \le \varepsilon$ for all unitary
$u, v$, in particular for all $u, v \in \mathrm{SO}(3, \mathbb{R})$.

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
theorem so3WordMapsSurjective_refuted : ¬ so3WordMapsSurjective := by
  obtain ⟨N, hN⟩ := exists_small_power
  obtain ⟨r, hr⟩ := half_turn
  obtain ⟨w, hw, h⟩ := smallOn_powers N (displacement r / 2) (by positivity)
  intro hs
  obtain ⟨⟨a, b⟩, hab⟩ := hs w hw.ne_one r
  have hbound := h (FreeGroup.lift ![a, b]) (by simpa using hN a)
  change displacement (wordMap SO w (a, b)) ≤ _ at hbound
  rw [hab] at hbound
  linarith

end MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted
