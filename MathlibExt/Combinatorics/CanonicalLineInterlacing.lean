/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import MathlibExt.Combinatorics.CanonicalLineEhrhart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interlacing on the canonical line

The symmetric basis polynomial `pBasis d 0` interlaces `pBasis (d + 1) 0` and its positive
perturbations by multiples of `(2 * X + 1) * pBasis d 0`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public noncomputable section

/-- **The basis polynomials $b^d_j$.** For natural numbers $d$ and $j$, $b^d_j$ is the complex
polynomial $b^d_j = \prod_{i=0}^{d-1} (X + d - j - i)$.

Integer constants are used before mapping to $\mathbb{C}$, avoiding any convention about rising
versus falling Pochhammer symbols.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `bᵈⱼ`.
-/
public def bBasis (d j : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range d, (X + C (((d : ℤ) - (j : ℤ) - (i : ℤ) : ℤ) : ℂ))

/-- **Symmetric basis polynomials.** For natural numbers $d$ and $j$, let $b^d_j$ be the complex
polynomial $\prod_{i=0}^{d-1} (X + d - j - i)$. The polynomial $p^d_j$ is $b^d_j$ if $2j = d$, and
$b^d_j + b^d_{d-j}$ otherwise, where $d - j$ is truncated at $0$ (so $p^d_j = b^d_j + b^d_0$ when
$j > d$).

Statements that use $p^d_j$ assume $j \le d$, where the truncation plays no role.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `pᵈⱼ`.
-/
public def pBasis (d j : ℕ) : Polynomial ℂ :=
  if 2 * j = d then bBasis d j else bBasis d j + bBasis d (d - j)

/-- **Interlacing lists.** Let $r$ be a binary relation on a type $\alpha$ and let $d \ge 0$.
A list $(a_1, \dots, a_d)$ interlaces a list $(b_1, \dots, b_{d+1})$ with respect to $r$ when
$b_1 \mathrel{r} a_1 \mathrel{r} b_2 \mathrel{r} \cdots \mathrel{r} a_d \mathrel{r} b_{d+1}$,
that is, $b_k \mathrel{r} a_k$ and $a_k \mathrel{r} b_{k+1}$ for $1 \le k \le d$. Two lists
interlace only when the second has exactly one more entry than the first; in particular the
empty list interlaces every one-element list.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of interlacing.
-/
public def ListInterlaces {α : Type*} (r : α → α → Prop) : List α → List α → Prop
  | [], [_] => True
  | a :: as, b :: b' :: bs => r b a ∧ r a b' ∧ ListInterlaces r as (b' :: bs)
  | _, _ => False

/-- **Interlacing on the canonical line.** A complex polynomial $f$ CL-interlaces a complex
polynomial $g$ when $f$ and $g$ are nonzero, $\deg g = \deg f + 1$, all roots of $f$ and of $g$
lie on the canonical line, and, writing $d = \deg f$ and listing the roots with multiplicity as
$a_1, \dots, a_d$ for $f$ and $b_1, \dots, b_{d+1}$ for $g$, each list sorted by increasing
imaginary part, they alternate:
$\operatorname{Im} b_1 \le \operatorname{Im} a_1 \le \operatorname{Im} b_2 \le \cdots \le
\operatorname{Im} a_d \le \operatorname{Im} b_{d+1}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-interlacing.
-/
public def CLInterlaces (f g : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ f.natDegree + 1 = g.natDegree ∧
    ∃ as bs : List ℂ,
      (as : Multiset ℂ) = f.roots ∧ (bs : Multiset ℂ) = g.roots ∧
        as.length = f.natDegree ∧ bs.length = g.natDegree ∧
        (∀ z ∈ as, z ∈ canonicalLine) ∧ (∀ z ∈ bs, z ∈ canonicalLine) ∧
        List.Pairwise (fun x y => x.im ≤ y.im) as ∧
        List.Pairwise (fun x y => x.im ≤ y.im) bs ∧
        ListInterlaces (fun x y => x.im ≤ y.im) as bs

namespace pBasis_zero_interlaces_perturbation

open Filter Real
open scoped Topology

private abbrev Width := Set.Ioi (0 : ℝ)

private def angle (a : Width) (t : ℝ) : ℝ := arctan (t / a) + π / 2

private def phase {n : ℕ} (a : Fin n → Width) (t : ℝ) : ℝ := ∑ i, angle (a i) t

private lemma phase_mono {n : ℕ} (a : Fin n → Width) (hn : 0 < n) : StrictMono (phase a) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro x y h
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  exact add_lt_add_left (arctan_strictMono (div_lt_div_of_pos_right h (a i).2)) _

-- The k-th root is at the unique height at which the phase is (k + 1/2)π.
private lemma exists_height {n : ℕ} (a : Fin n → Width) (k : Fin n) :
    ∃ t, phase a t = ((k.val : ℝ) + 1 / 2) * π := by
  have hbot : Tendsto (phase a) atBot (𝓝 (∑ _ : Fin n, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro i _
    have h := tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
    unfold angle
    simpa [Function.comp_def] using
      ((h.comp ((tendsto_div_const_atBot_of_pos (a i).2).2 tendsto_id)).add_const (π / 2))
  have htop : Tendsto (phase a) atTop (𝓝 (∑ _ : Fin n, π)) := by
    apply tendsto_finsetSum
    intro i _
    have h := tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    unfold angle
    simpa [Function.comp_def, add_halves] using
      ((h.comp ((tendsto_div_const_atTop_of_pos (a i).2).2 tendsto_id)).add_const (π / 2))
  apply mem_range_of_exists_le_of_exists_ge
  · unfold phase angle
    fun_prop
  · refine (hbot.eventually_le_const ?_).exists
    simp only [Finset.sum_const_zero]
    positivity
  · refine (htop.eventually_const_le ?_).exists
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply mul_lt_mul_of_pos_right _ pi_pos
    have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    linarith

private def height {n : ℕ} (a : Fin n → Width) (k : Fin n) : ℝ := (exists_height a k).choose

private lemma phase_height {n : ℕ} (a : Fin n → Width) (k : Fin n) :
    phase a (height a k) = ((k.val : ℝ) + 1 / 2) * π := (exists_height a k).choose_spec

private lemma height_mono {n : ℕ} (a : Fin n → Width) : StrictMono (height a) := by
  intro i j hij
  apply (phase_mono a (Nat.zero_lt_of_lt i.isLt)).lt_iff_lt.mp
  rw [phase_height, phase_height]
  exact mul_lt_mul_of_pos_right (add_lt_add_left (by exact_mod_cast hij : (i.val : ℝ) < j.val) _)
    pi_pos

private def point (t : ℝ) : ℂ := ⟨-(1 / 2), t⟩

private def factors {n : ℕ} (a : Fin n → Width) (s : ℂ) : ℂ[X] :=
  ∏ i, (X + C (1 / 2 + s * ((a i : ℝ) : ℂ)))

private def paired {n : ℕ} (a : Fin n → Width) := factors a 1 + factors a (-1)

private lemma degree_paired {n : ℕ} (a : Fin n → Width) : (paired a).degree = n := by
  have monic (s : ℂ) : (factors a s).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _
  have deg (s : ℂ) : (factors a s).degree = n := by
    rw [degree_eq_natDegree (monic s).ne_zero]
    unfold factors
    rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  rw [paired, degree_add_eq_of_leadingCoeff_add_ne_zero, deg, deg, max_self]
  rw [(monic _).leadingCoeff, (monic _).leadingCoeff]
  norm_num

-- The two linear factors at height t differ by a rotation through twice the angle.
private lemma rotate_factor (a : Width) (t : ℝ) :
    Complex.exp ((2 * (angle a t : ℂ)) * Complex.I) * (Complex.I * t - (a : ℝ)) =
      Complex.I * t + (a : ℝ) := by
  let u := arctan (t / a)
  have hs : sin u * (a : ℝ) = cos u * t := by
    have h := tan_arctan (t / a)
    rw [tan_eq_sin_div_cos] at h
    have h' := (div_eq_div_iff (cos_arctan_pos _).ne' a.2.ne').mp h
    simpa [u, mul_comm] using h'
  have rot : Complex.exp ((u : ℂ) * Complex.I) * ((a : ℝ) - Complex.I * t) =
      Complex.exp (-((u : ℂ) * Complex.I)) * ((a : ℝ) + Complex.I * t) := by
    apply Complex.ext <;>
      simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
    linarith
  have hexp : 2 * (angle a t : ℂ) * Complex.I =
      (u : ℂ) * Complex.I + (u : ℂ) * Complex.I + (π : ℂ) * Complex.I := by
    simp only [angle, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat, u]
    ring
  rw [hexp, Complex.exp_add_pi_mul_I, Complex.exp_add]
  calc
    _ = Complex.exp ((u : ℂ) * Complex.I) *
        (Complex.exp ((u : ℂ) * Complex.I) * ((a : ℝ) - Complex.I * t)) := by ring
    _ = _ := by rw [rot, ← mul_assoc, ← Complex.exp_add]; simp [add_comm]

private lemma eval_factors {n : ℕ} (a : Fin n → Width) (t : ℝ) :
    (factors a 1).eval (point t) =
      Complex.exp (2 * (phase a t : ℂ) * Complex.I) * (factors a (-1)).eval (point t) := by
  have hp : point t = Complex.I * t - 1 / 2 := by
    apply Complex.ext <;> norm_num [point, Complex.mul_re, Complex.mul_im]
  have he : 2 * (phase a t : ℂ) * Complex.I =
      ∑ i, 2 * (angle (a i) t : ℂ) * Complex.I := by
    simp [phase, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum]
  rw [he, Complex.exp_sum]
  simp only [factors, eval_prod, eval_add, eval_X, eval_C, one_mul, neg_one_mul, hp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  convert (rotate_factor (a i) t).symm using 1 <;> ring

private lemma eval_height {n : ℕ} (a : Fin n → Width) (k : Fin n) :
    (paired a).eval (point (height a k)) = 0 := by
  rw [paired, eval_add, eval_factors, phase_height]
  have he : 2 * ((((k.val : ℝ) + 1 / 2) * π : ℝ) : ℂ) * Complex.I =
      k.val * (2 * (π : ℂ) * Complex.I) + (π : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I]
  ring

private lemma interlaces_ofFn {α : Type*} (r : α → α → Prop) {n : ℕ}
    (f : Fin n → α) (g : Fin (n + 1) → α)
    (h : ∀ i, r (g i.castSucc) (f i) ∧ r (f i) (g i.succ)) :
    ListInterlaces r (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp [List.ofFn_succ, ListInterlaces]
  | succ n ih =>
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g),
      List.ofFn_succ (f := fun i => g i.succ)]
    refine ⟨(h 0).1, (h 0).2, ?_⟩
    rw [← List.ofFn_succ (f := fun i => g i.succ)]
    exact ih _ _ (fun i => h i.succ)

private def rootList {n : ℕ} (a : Fin n → Width) := List.ofFn fun i => point (height a i)

private lemma roots_paired {n : ℕ} (a : Fin n → Width) :
    (rootList a : Multiset ℂ) = (paired a).roots := by
  let S : Finset ℂ := ⟨rootList a, List.nodup_ofFn.mpr fun i j h =>
    (height_mono a).injective (congrArg Complex.im h)⟩
  symm
  apply roots_eq_of_degree_eq_card (S := S)
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (show x ∈ rootList a from hx)
    exact eval_height a i
  · simp [S, rootList, degree_paired]

private lemma interlace_heights {n : ℕ} (a : Fin n → Width) (b : Width) :
    ListInterlaces (fun x y : ℂ => x.im ≤ y.im) (rootList a) (rootList (Fin.cons b a)) := by
  apply interlaces_ofFn
  intro i
  change height (Fin.cons b a) i.castSucc ≤ height a i ∧
    height a i ≤ height (Fin.cons b a) i.succ
  have hm := phase_mono (Fin.cons b a) (Nat.succ_pos n)
  have hadd (t : ℝ) : phase (Fin.cons b a) t = angle b t + phase a t := by
    simp [phase, Fin.sum_univ_succ]
  have hlo := neg_pi_div_two_lt_arctan (height a i / b)
  have hhi := arctan_lt_pi_div_two (height a i / b)
  constructor <;> apply hm.le_iff_le.mp <;>
    simp only [phase_height, hadd (height a i), Fin.val_castSucc, Fin.val_succ, Nat.cast_add,
      Nat.cast_one, angle] <;> linarith

private lemma factors_cons {n : ℕ} (a : Fin n → Width) (b : Width) (s : ℂ) :
    factors (Fin.cons b a) s = (X + C (1 / 2 + s * (b : ℝ))) * factors a s := by
  simp [factors, Fin.prod_univ_succ]

private def halfWidth (d : ℕ) : Width := ⟨d + 1 / 2, show (0 : ℝ) < d + 1 / 2 by positivity⟩

private def widths : (d : ℕ) → Fin d → Width
  | 0 => Fin.elim0
  | d + 1 => Fin.cons (halfWidth d) (widths d)

private lemma base_factors (d : ℕ) :
    bBasis d 0 = factors (widths d) 1 ∧ bBasis d d = factors (widths d) (-1) := by
  induction d with
  | zero => simp [bBasis, factors]
  | succ d ih =>
    simp only [widths, factors_cons, ← ih.1, ← ih.2]
    constructor
    · rw [bBasis, Finset.prod_range_succ']
      simp only [bBasis, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul,
        add_sub_add_right_eq_sub, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [mul_comm]
      congr 2
      push_cast [halfWidth]
      apply congrArg C
      ring
    · rw [bBasis, Finset.prod_range_succ_comm]
      simp only [bBasis, sub_self, zero_sub, Int.cast_neg, Int.cast_natCast, neg_one_mul]
      congr 2
      push_cast [halfWidth]
      apply congrArg C
      ring

private lemma basis_eq_paired (d : ℕ) (hd : 0 < d) : pBasis d 0 = paired (widths d) := by
  simp [pBasis, hd.ne, base_factors, paired]

private lemma paired_interlaces {n : ℕ} (a : Fin n → Width) (b : Width) (c : ℂ) (hc : c ≠ 0) :
    CLInterlaces (paired a) (C c * paired (Fin.cons b a)) := by
  have deg {m : ℕ} (v : Fin m → Width) : (paired v).natDegree = m :=
    natDegree_eq_of_degree_eq_some (degree_paired v)
  have nz {m : ℕ} (v : Fin m → Width) : paired v ≠ 0 := by
    exact ne_zero_of_degree_gt (by rw [degree_paired]; exact WithBot.bot_lt_coe m)
  have line {m : ℕ} (v : Fin m → Width) : ∀ z ∈ rootList v, z ∈ canonicalLine :=
    List.forall_mem_ofFn_iff.mpr fun _ => rfl
  have sorted {m : ℕ} (v : Fin m → Width) :
      (rootList v).Pairwise (fun x y => x.im ≤ y.im) :=
    List.pairwise_ofFn.mpr fun _ _ hij => ((height_mono v) hij).le
  refine ⟨nz a, mul_ne_zero (C_ne_zero.mpr hc) (nz _), ?_, rootList a,
    rootList (Fin.cons b a), roots_paired a, ?_, ?_, ?_, line a, line _, sorted a, sorted _,
    interlace_heights a b⟩
  · simp only [natDegree_C_mul hc, deg]
  · rw [roots_C_mul _ hc, roots_paired]
  · simp [rootList, deg]
  · simp [rootList, deg, natDegree_C_mul hc]

end pBasis_zero_interlaces_perturbation

open pBasis_zero_interlaces_perturbation in
/-- **$p^d_0$ CL-interlaces $p^{d+1}_0$.** For every natural number $d \ge 1$, the symmetric
basis polynomial $p^d_0$ CL-interlaces $p^{d+1}_0$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 4.
-/
public theorem pBasis_zero_interlaces_succ (d : ℕ) (hd : 0 < d) :
    CLInterlaces (pBasis d 0) (pBasis (d + 1) 0) := by
  rw [basis_eq_paired d hd, basis_eq_paired (d + 1) (Nat.succ_pos d)]
  simpa only [widths, C_1, one_mul] using
    paired_interlaces (widths d) (halfWidth d) 1 one_ne_zero

open pBasis_zero_interlaces_perturbation in
/-- **CL-interlacing of $p^d_0$ with a perturbation of $p^{d+1}_0$.** For every natural number
$d \ge 1$ and every real number $w > 0$, the symmetric basis polynomial $p^d_0$ CL-interlaces
the polynomial $p^{d+1}_0 + w \, (2X + 1) \, p^d_0$.

The orientation follows the numbered statement in the INTEGERS version; the arXiv wording
differs.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 5.
-/
public theorem pBasis_zero_interlaces_perturbation (d : ℕ) (hd : 0 < d)
    (w : ℝ) (hw : 0 < w) :
    CLInterlaces (pBasis d 0)
      (pBasis (d + 1) 0 + C (w : ℂ) * (2 * X + 1) * pBasis d 0) := by
  let c : ℝ := 1 + 2 * w
  have hc : 0 < c := by dsimp [c]; positivity
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let b : Width := ⟨(halfWidth d : ℝ) / c, div_pos (halfWidth d).2 hc⟩
  rw [basis_eq_paired d hd, basis_eq_paired (d + 1) (by omega)]
  have scale (s : ℂ) :
      X + C (1 / 2 + s * (halfWidth d : ℝ)) + C (w : ℂ) * (2 * X + 1) =
        C (c : ℂ) * (X + C (1 / 2 + s * (b : ℝ))) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_X, eval_C, eval_mul, eval_ofNat, eval_one]
    change _ = (c : ℂ) * (x + (1 / 2 + s * (((halfWidth d : ℝ) / c : ℝ) : ℂ)))
    rw [Complex.ofReal_div]
    field_simp
    push_cast [c]
    ring
  convert paired_interlaces (widths d) b (c : ℂ) hc' using 1
  unfold paired
  simp only [widths, factors_cons]
  linear_combination (factors (widths d) 1) * scale 1 + (factors (widths d) (-1)) * scale (-1)

end
end MetaMathlibExt
