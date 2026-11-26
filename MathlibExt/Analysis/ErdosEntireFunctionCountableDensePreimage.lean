/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.LinearCombination

/-!
# Realizing countable dense sets as fibers of an entire function (AMR-022-2031)

Erdos asked whether, for any two countable dense plane sets `A` and `B`,
some entire function takes values in `B` exactly on `A`.

The theorem `conjecture_holds` realizes this preimage by a locally uniform limit of polynomials.
-/

@[expose] public section

namespace MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted

/-! Source record `AMR-022-2031`. -/

/-- **Erdős's problem on countable dense preimages.** This is the statement that for any two
countable dense subsets $A$ and $B$ of $\mathbb{C}$, there is an entire function
$f : \mathbb{C} \to \mathbb{C}$ such that for every $z \in \mathbb{C}$, $f(z) \in B$ if and only
if $z \in A$; that is, $f^{-1}(B) = A$.

Source: Research Problems in Function Theory, Problem 2.31 (record AMR-022-2031). -/
def conjecture : Prop :=
  ∀ A B : Set ℂ, A.Countable → Dense A → B.Countable → Dense B →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Set.univ ∧ ∀ z, (f z ∈ B ↔ z ∈ A)

open Set Metric Filter Polynomial
open scoped Topology

private theorem exists_small_multiple {K : Set ℂ} (hK : IsCompact K) (p : ℂ[X])
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, δ * ‖p.eval z‖ ≤ ε := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn p.continuous.continuousOn
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨ε / D, by positivity, fun z hz => ?_⟩
  calc
    _ ≤ ε / D * D := by gcongr; exact (hM z hz).trans (le_max_left _ _)
    _ = ε := div_mul_cancel₀ _ hD.ne'

-- The roots of s are the points to be fixed at later stages. The last inequality
-- controls all other preimages on the disk, including points very close to those roots.
private def CanMove (A K : Set ℂ) (w p : ℂ[X]) : Prop :=
  ∀ ε > (0 : ℝ), ∃ q s : ℂ[X], (∀ z ∈ K, ‖q.eval z‖ ≤ ε) ∧
    (∀ z, s.eval z = 0 → z ∈ A ∧ (p + w * q).eval z = 0) ∧
    ∀ z ∈ K, ‖s.eval z‖ ≤ ‖(p + w * q).eval z‖

private theorem canMove_mul {A K : Set ℂ} {w p v : ℂ[X]} (hK : IsCompact K)
    (hp : CanMove A K w p) (hv : CanMove A K w v) : CanMove A K w (p * v) := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := exists_small_multiple hK v (half_pos hε)
  obtain ⟨q, s, hq, hs, hsp⟩ := hp δ hδ
  obtain ⟨η, hη, he⟩ := exists_small_multiple hK (p + w * q) (half_pos hε)
  obtain ⟨t, u, ht, hu, huv⟩ := hv η hη
  let m := q * v + t * (p + w * q)
  have hm : p * v + w * m = (p + w * q) * (v + w * t) := by dsimp [m]; ring
  refine ⟨m, s * u, ?_, ?_, ?_⟩
  · intro z hz
    simp only [m, eval_add, eval_mul]
    calc
      _ ≤ ‖q.eval z‖ * ‖v.eval z‖ + ‖t.eval z‖ * ‖(p + w * q).eval z‖ := by
        simpa only [eval_add, eval_mul, norm_mul] using
          norm_add_le ((q * v).eval z) ((t * (p + w * q)).eval z)
      _ ≤ δ * ‖v.eval z‖ + η * ‖(p + w * q).eval z‖ := by
        gcongr <;> first | exact hq z hz | exact ht z hz
      _ ≤ ε := by linarith [hd z hz, he z hz]
  · intro z hz
    rw [hm, eval_mul]
    rw [eval_mul] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact ⟨(hs z h).1, mul_eq_zero_of_left (hs z h).2 _⟩
    · exact ⟨(hu z h).1, mul_eq_zero_of_right _ (hu z h).2⟩
  · intro z hz
    rw [hm, eval_mul, eval_mul, norm_mul, norm_mul]
    exact mul_le_mul (hsp z hz) (huv z hz) (norm_nonneg _) (norm_nonneg _)

private theorem canMove_linear {A : Set ℂ} (hA : Dense A) (R : ℝ) (w : ℂ[X])
    (hw : ∀ z, w.eval z = 0 → z ∈ A) (r : ℂ) :
    CanMove A (closedBall 0 R) w (X - C r) := by
  intro ε hε
  by_cases hr : r ∈ A
  · refine ⟨0, X - C r, fun _ _ => by simpa using hε.le, ?_, by simp⟩
    intro z hz
    have := sub_eq_zero.mp (by simpa using hz : z - r = 0)
    simp [this, hr]
  -- Choose a near r so that z - r + t(a) w(z) vanishes at a. A Lipschitz bound for w
  -- gives a lower bound of |z - a| / 2 for this perturbed factor throughout the disk.
  have hwr : w.eval r ≠ 0 := fun h => hr (hw r h)
  let D := max R (‖r‖ + 1)
  have hreg : ContDiff ℂ 1 w.eval := by
    convert w.contDiff_aeval (𝕜 := ℂ) 1 using 1
    ext x
    exact (congrFun (coe_aeval_eq_eval x) w).symm
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : ℂ) D) hreg.locallyLipschitz.locallyLipschitzOn
  let t (a : ℂ) := (r - a) / w.eval a
  have ht : Tendsto t (𝓝 r) (𝓝 0) := by
    have hc : ContinuousAt t r := by
      exact (continuousAt_const.sub continuousAt_id).div w.continuous.continuousAt hwr
    have htr : t r = 0 := by simp [t]
    exact htr ▸ hc.tendsto
  have hsmall : ∀ᶠ a in 𝓝 r, ‖t a‖ < ε := ht.norm.eventually_lt_const (by simpa using hε)
  have hlip : ∀ᶠ a in 𝓝 r, ‖t a‖ * L < 1 / 2 :=
    (ht.norm.mul_const (L : ℝ)).eventually_lt_const (by norm_num)
  have hball : ∀ᶠ a : ℂ in 𝓝 r, ‖a‖ < D :=
    continuous_norm.continuousAt.eventually_lt_const
      (lt_of_lt_of_le (lt_add_one ‖r‖) (le_max_right _ _))
  obtain ⟨a, ha, hsa, hla, hba, hwa⟩ :=
    ((mem_closure_iff_frequently.mp (hA r)).and_eventually
      (hsmall.and (hlip.and (hball.and (w.continuous.continuousAt.eventually_ne hwr))))).exists
  have hta : t a * w.eval a = r - a := div_mul_cancel₀ _ hwa
  refine ⟨C (t a), C (2 : ℂ)⁻¹ * (X - C a), fun z _ => by simpa using hsa.le, ?_, ?_⟩
  · intro z hz
    have hza : z = a := by simpa [sub_eq_zero] using hz
    subst z
    refine ⟨ha, ?_⟩
    simp only [eval_add, eval_sub, eval_X, eval_C, eval_mul]
    linear_combination hta
  · intro z hz
    have haz : a ∈ closedBall (0 : ℂ) D := by simpa using hba.le
    have hzz := closedBall_subset_closedBall (le_max_left R (‖r‖ + 1)) hz
    have hdist := hL.dist_le_mul z hzz a haz
    rw [dist_eq_norm, dist_eq_norm] at hdist
    have heq : z - a = (z - r + w.eval z * t a) - t a * (w.eval z - w.eval a) := by
      linear_combination -hta
    have htri := norm_sub_le (z - r + w.eval z * t a) (t a * (w.eval z - w.eval a))
    rw [← heq, norm_mul] at htri
    have hbound : ‖t a‖ * ‖w.eval z - w.eval a‖ ≤ (1 / 2 : ℝ) * ‖z - a‖ := calc
      _ ≤ ‖t a‖ * ((L : ℝ) * ‖z - a‖) := by gcongr
      _ = (‖t a‖ * L) * ‖z - a‖ := (mul_assoc ..).symm
      _ ≤ _ := by gcongr
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_add, norm_mul, norm_inv]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith

private theorem canMove_poly {A : Set ℂ} (hA : Dense A) (R : ℝ) (w p : ℂ[X])
    (hw : ∀ z, w.eval z = 0 → z ∈ A) : CanMove A (closedBall 0 R) w p := by
  have hc (v : ℂ) : CanMove A (closedBall 0 R) w (C v) := by
    intro ε hε
    by_cases hv : v = 0
    · let t : ℂ := (ε : ℂ)
      have ht : t ≠ 0 := by simpa [t] using hε.ne'
      refine ⟨C t, w * C t, fun _ _ => by simp [t, abs_of_pos hε], ?_, ?_⟩
      · intro z hz
        simp only [eval_mul, eval_C, mul_eq_zero, ht, or_false] at hz
        exact ⟨hw z hz, by simp [hv, hz]⟩
      · simp [hv]
    · exact ⟨0, C v, fun _ _ => by simpa using hε.le, by simp [hv], by simp⟩
  have hm (m : Multiset ℂ) : CanMove A (closedBall 0 R) w ((m.map (X - C ·)).prod) := by
    induction m using Multiset.induction_on with
    | empty => simpa using hc 1
    | cons r m ih =>
      simpa using canMove_mul (isCompact_closedBall _ _) (canMove_linear hA R w hw r) ih
  exact (IsAlgClosed.splits p).eq_prod_roots ▸
    canMove_mul (isCompact_closedBall _ _) (hc p.leadingCoeff) (hm p.roots)

-- At z the permitted values form a closed ball centered at p(z) of radius |w(z)|.
-- A root of w therefore specifies an interpolation value exactly.
private structure Stage (A B : Set ℂ) where
  p : ℂ[X]
  w : ℂ[X]
  locked : ∀ z, w.eval z = 0 → z ∈ A ∧ p.eval z ∈ B

private noncomputable def Stage.values {A B : Set ℂ} (s : Stage A B) (z : ℂ) : Set ℂ :=
  closedBall (s.p.eval z) ‖s.w.eval z‖

private theorem exists_small_interpolation {B : Set ℂ} (hB : Dense B) (x u : ℂ)
    (hx : u = 0 → x ∈ B) :
    ∃ t : ℂ, ‖t‖ ≤ 1 / 4 ∧ x + u * t ∈ B := by
  by_cases hu : u = 0
  · exact ⟨0, by norm_num, by simpa using hx hu⟩
  have hlim : ContinuousAt (fun y : ℂ => (y - x) / u) x := by fun_prop
  have hsmall : ∀ᶠ y in 𝓝 x, ‖(y - x) / u‖ < 1 / 4 :=
    hlim.norm.eventually_lt_const (by norm_num)
  obtain ⟨y, hy, ht⟩ := ((mem_closure_iff_frequently.mp (hB x)).and_eventually hsmall).exists
  exact ⟨(y - x) / u, ht.le, by convert hy using 1; field_simp; ring⟩

-- One step fixes the image of a and controls the whole fiber over b inside the disk.
private theorem exists_refinement {A B : Set ℂ} (hA : Dense A) (hB : Dense B) (d : Stage A B)
    {a b : ℂ} (ha : a ∈ A) (hb : b ∈ B) (R ε : ℝ) (hε : 0 < ε) :
    ∃ e : Stage A B, ∀ z ∈ closedBall 0 R, e.values z ⊆ d.values z ∧
      ‖e.w.eval z‖ ≤ ε ∧ (∀ y ∈ e.values z, (z = a → y ∈ B) ∧ (y = b → z ∈ A)) := by
  let k : ℂ[X] := X - C a
  let v := d.w * k
  obtain ⟨t, ht, hta⟩ :=
    exists_small_interpolation hB (d.p.eval a) (d.w.eval a) (fun h => (d.locked a h).2)
  let p := d.p + d.w * C t
  have hv z (hz : v.eval z = 0) : z ∈ A ∧ p.eval z ∈ B := by
    simp only [v, k, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hz
    rcases hz with h | rfl
    · exact ⟨(d.locked z h).1, by simpa [p, h] using (d.locked z h).2⟩
    · exact ⟨ha, by simpa [p] using hta⟩
  have hK := isCompact_closedBall (0 : ℂ) R
  obtain ⟨δ, hδ, hd⟩ := exists_small_multiple hK k (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨q, s, hq, hs, hsep⟩ := canMove_poly hA R v (p - C b) (fun z hz => (hv z hz).1) δ hδ
  let P := p + v * q
  have hPb z : P.eval z - b = ((p - C b) + v * q).eval z := by simp [P]; ring
  -- The next radius must fit inside the previous ball, stay below half the lower bound
  -- for |P - b| off the new roots, and satisfy the uniform tolerance ε.
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_small_multiple hK (k * s) (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨c₂, hc₂, hc₂'⟩ := exists_small_multiple hK v (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨c₃, hc₃, hc₃'⟩ := exists_small_multiple hK (v * s) hε
  let c := min c₁ (min c₂ c₃)
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂ hc₃)
  let W := C (c : ℂ) * (v * s)
  have hW z : ‖W.eval z‖ = c * (‖v.eval z‖ * ‖s.eval z‖) := by
    simp [W, abs_of_pos hc]
  have locked z (hz : W.eval z = 0) : z ∈ A ∧ P.eval z ∈ B := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    simp only [W, eval_mul, eval_C, mul_eq_zero, hc', false_or] at hz
    rcases hz with h | h
    · exact ⟨(hv z h).1, by simpa [P, h] using (hv z h).2⟩
    · exact ⟨(hs z h).1, (sub_eq_zero.mp ((hPb z).trans (hs z h).2)).symm ▸ hb⟩
  refine ⟨⟨P, W, locked⟩, fun z hz => ?_⟩
  have h₁ : ‖W.eval z‖ ≤ ‖d.w.eval z‖ * (1 / 2) := calc
    _ = ‖d.w.eval z‖ * (c * ‖(k * s).eval z‖) := by rw [hW]; simp [v]; ring
    _ ≤ ‖d.w.eval z‖ * (c₁ * ‖(k * s).eval z‖) := by gcongr; exact min_le_left _ _
    _ ≤ _ := by gcongr; exact hc₁' z hz
  have h₂ : ‖W.eval z‖ ≤ 1 / 2 * ‖s.eval z‖ := calc
    _ = c * ‖v.eval z‖ * ‖s.eval z‖ := by rw [hW, mul_assoc]
    _ ≤ c₂ * ‖v.eval z‖ * ‖s.eval z‖ := by gcongr; exact (min_le_right ..).trans (min_le_left ..)
    _ ≤ _ := by gcongr; exact hc₂' z hz
  have h₃ : ‖W.eval z‖ ≤ ε := calc
    _ = c * ‖(v * s).eval z‖ := by simp [hW]
    _ ≤ c₃ * ‖(v * s).eval z‖ := by gcongr; exact (min_le_right ..).trans (min_le_right ..)
    _ ≤ _ := hc₃' z hz
  refine ⟨?_, h₃, ?_⟩
  · intro y hy
    change dist y (P.eval z) ≤ ‖W.eval z‖ at hy
    change dist y (d.p.eval z) ≤ ‖d.w.eval z‖
    have hp : dist (p.eval z) (d.p.eval z) ≤ ‖d.w.eval z‖ * (1 / 4) := by
      simpa [p, dist_eq_norm, norm_mul] using mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    have hvq : dist (P.eval z) (p.eval z) ≤ ‖d.w.eval z‖ * (1 / 4) := calc
      _ = ‖d.w.eval z‖ * (‖q.eval z‖ * ‖k.eval z‖) := by simp [P, v, dist_eq_norm]; ring
      _ ≤ ‖d.w.eval z‖ * (δ * ‖k.eval z‖) := by gcongr; exact hq z hz
      _ ≤ _ := by gcongr; exact hd z hz
    linarith [dist_triangle y (P.eval z) (d.p.eval z),
      dist_triangle (P.eval z) (p.eval z) (d.p.eval z)]
  · intro y hy
    change dist y (P.eval z) ≤ ‖W.eval z‖ at hy
    constructor
    · rintro rfl
      have hzero : W.eval z = 0 := by simp [W, v, k]
      rw [hzero, norm_zero, dist_le_zero] at hy
      exact hy ▸ (locked z hzero).2
    · rintro rfl
      rw [dist_comm, dist_eq_norm, hPb] at hy
      exact (hs z (norm_eq_zero.mp (by linarith [hsep z hz, norm_nonneg (s.eval z)]))).1

private theorem limit_of_stages {A B : Set ℂ} (d : ℕ → Stage A B)
    (hnest : ∀ (n : ℕ) z, ‖z‖ ≤ n + 1 → (d (n + 1)).values z ⊆ (d n).values z)
    (hwidth : ∀ (n : ℕ) z, ‖z‖ ≤ n → ‖(d n).w.eval z‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f univ ∧
      ∀ (n : ℕ) z, ‖z‖ ≤ n → f z ∈ (d n).values z := by
  have sub {n m : ℕ} (hnm : n ≤ m) {z : ℂ} (hz : ‖z‖ ≤ n) :
      (d m).values z ⊆ (d n).values z := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact (hnest m z (by linarith)).trans ih
  have center (z : ℂ) (n : ℕ) : (d n).p.eval z ∈ (d n).values z :=
    mem_closedBall_self (norm_nonneg _)
  have small (r ε : ℝ) (hε : 0 < ε) :
      ∃ n : ℕ, r < n ∧ (1 / 2 : ℝ) ^ n < ε := by
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    exact ((tendsto_natCast_atTop_atTop.eventually_gt_atTop r).and
      (hlim.eventually_lt_const hε)).exists
  have hc (z : ℂ) : CauchySeq (fun n => (d n).p.eval z) := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨n, hn, hεn⟩ := small ‖z‖ ε hε
    refine ⟨n, fun m hm => ?_⟩
    exact ((mem_closedBall.mp (sub hm hn.le (center z m))).trans (hwidth n z hn.le)).trans_lt hεn
  choose f hf using fun z => cauchySeq_tendsto_of_complete (hc z)
  have hmem (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ n) : f z ∈ (d n).values z :=
    isClosed_closedBall.mem_of_tendsto (hf z) <|
      (eventually_ge_atTop n).mono fun m hm => sub hm hz (center z m)
  have hloc : TendstoLocallyUniformly (fun n => (d n).p.eval) f atTop := by
    refine Metric.tendstoLocallyUniformly_iff.mpr fun ε hε x => ?_
    obtain ⟨n, hn, hεn⟩ := small ‖x‖ (ε / 2) (half_pos hε)
    refine ⟨ball (0 : ℂ) n, isOpen_ball.mem_nhds (by simpa using hn), ?_⟩
    filter_upwards [eventually_ge_atTop n] with m hm y hy
    have hyn : ‖y‖ ≤ n := by simpa using (ball_subset_closedBall hy : y ∈ closedBall 0 n)
    have h₁ := mem_closedBall.mp (hmem n y hyn)
    have h₂ := mem_closedBall.mp (sub hm hyn (center y m))
    linarith [dist_triangle_right (f y) ((d m).p.eval y) ((d n).p.eval y), hwidth n y hyn]
  exact ⟨f, hloc.tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun n => (d n).p.differentiableOn) isOpen_univ, hmem⟩

/--
**Every countable dense set is a preimage of any other under an entire function.** For any two
countable dense subsets $A$ and $B$ of $\mathbb{C}$, there is an entire function
$f : \mathbb{C} \to \mathbb{C}$ such that for every $z \in \mathbb{C}$, $f(z) \in B$ if and only
if $z \in A$; that is, $f^{-1}(B) = A$.

Hayman's update to Problem 2.31 reports that Barth and Schneider constructed such functions.

Source: K. F. Barth and W. J.
Schneider, Entire functions mapping arbitrary countable dense sets and their complements onto
each other, J. London Math. Soc. (2) 4 (1972), 482-488, https://doi.org/10.1112/jlms/s2-4.3.482.
Moved from `OpenConjectures/Analysis/ErdosEntireFunctionCountableDensePreimage`.
-/
public theorem conjecture_holds : conjecture := by
  intro A B hAc hA hBc hB
  obtain ⟨a, ha⟩ := hAc.exists_eq_range hA.nonempty
  obtain ⟨b, hb⟩ := hBc.exists_eq_range hB.nonempty
  have step (n : ℕ) (s : Stage A B) :=
    exists_refinement hA hB s (a := a n.unpair.1) (b := b n.unpair.1)
      (ha ▸ mem_range_self _) (hb ▸ mem_range_self _) (n + 1) ((1 / 2) ^ (n + 1)) (by positivity)
  let d : ℕ → Stage A B := Nat.rec ⟨0, 1, by simp⟩ fun n s => (step n s).choose
  have spec (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ n + 1) :=
    (step n (d n)).choose_spec z (by simpa using hz)
  obtain ⟨f, hf, hmem⟩ := limit_of_stages d (fun n z hz => (spec n hz).1) (by
    rintro (_ | n) z hz
    · simp [d]
    · exact (spec n (by simpa using hz)).2.1)
  refine ⟨f, hf, fun z => ?_⟩
  -- Pairing the index with arbitrarily large radii exhausts each fiber on the whole plane.
  have test (i : ℕ) : (z = a i → f z ∈ B) ∧ (f z = b i → z ∈ A) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖z‖
    let n := Nat.pair i k
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.right_le_pair i k
    have hz : ‖z‖ ≤ n + 1 := by linarith
    have h := (spec n hz).2.2 (f z) (hmem (n + 1) z (by simpa using hz))
    simpa [n] using h
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := hb ▸ hz
    exact (test i).2 hi.symm
  · intro hz
    obtain ⟨i, hi⟩ := ha ▸ hz
    exact (test i).1 hi.symm

end MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted
