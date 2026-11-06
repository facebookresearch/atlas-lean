/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RealRooted
public import MathlibExt.Algebra.MvPolynomial.PDeriv

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.List.OfFn
import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section

open scoped BigOperators ComplexOrder
namespace MvPolynomial

/-- **Stable polynomials.** A complex multivariate polynomial is stable if it has no zero when
every variable lies in the open upper half-plane. -/
public def IsStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).im) → eval z p ≠ 0

/-- **Real stable polynomials.** A complex multivariate polynomial is real stable if it is stable
and has real coefficients. -/
public def IsRealStable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  map (starRingEnd ℂ) p = p ∧ p.IsStable

/-- **Univariate specialization.** Let $R$ be a commutative ring, let $p$ be a multivariate
polynomial over $R$ in variables $X_j$ indexed by $j \in \sigma$, and let $i \in \sigma$ and
$x : \sigma \to R$. The univariate specialization of $p$ at $i$ and $x$ is the polynomial in
$R[X]$ obtained from $p$ by substituting $X$ for $X_i$ and the constant $x_j$ for every $X_j$ with
$j \ne i$; the value $x_i$ is not used. -/
public noncomputable def univariateSpecialization {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (x : σ → R) (p : MvPolynomial σ R) : Polynomial R :=
  eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j)) p

/-- **Partial derivatives under univariate specialization.** Let $R$ be a commutative ring, let
$p$ be a multivariate polynomial over $R$ in variables $X_j$ indexed by $j \in \sigma$, let
$i \in \sigma$ and $x : \sigma \to R$, and for a polynomial $q$ write $q_{i,x} \in R[X]$ for its
univariate specialization that keeps $X_i$ as the variable $X$ and sets every other $X_j$ to
$x_j$. Then $(\partial p / \partial X_i)_{i,x} = (p_{i,x})'$, the derivative of $p_{i,x}$. -/
public theorem derivative_univariateSpecialization {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (x : σ → R) (p : MvPolynomial σ R) :
    univariateSpecialization i x (pderiv i p) =
      Polynomial.derivative (univariateSpecialization i x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [univariateSpecialization]
  | add p q hp hq =>
      simp only [univariateSpecialization] at hp hq ⊢
      simp only [map_add]
      rw [hp, hq]
  | mul_X p j hp =>
      simp only [univariateSpecialization] at hp ⊢
      by_cases hji : j = i
      · subst j
        simp only [pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, eval₂Hom_X',
          Polynomial.derivative_mul]
        rw [hp]
        simp
      · simp only [pderiv_mul, pderiv_X_of_ne hji, mul_zero, add_zero, map_mul,
          eval₂Hom_X', Polynomial.derivative_mul]
        simp only [hji, ↓reduceIte, Polynomial.derivative_C, mul_zero, add_zero]
        rw [hp]

/-- **Evaluating a univariate specialization.** Let $R$ be a commutative ring, let $p$ be a
multivariate polynomial over $R$ in variables $X_j$ indexed by $j \in \sigma$, and let
$i \in \sigma$, $x : \sigma \to R$ and $t \in R$. Evaluating at $t$ the univariate specialization
of $p$ that keeps $X_i$ as the variable and sets every other $X_j$ to $x_j$ gives $p(y)$, where
$y_i = t$ and $y_j = x_j$ for $j \ne i$. -/
public theorem eval_univariateSpecialization {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (x : σ → R) (t : R) (p : MvPolynomial σ R) :
    Polynomial.eval t (univariateSpecialization i x p) =
      MvPolynomial.eval (Function.update x i t) p := by
  change (Polynomial.evalRingHom t)
    ((eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j))) p) = _
  change ((Polynomial.evalRingHom t).comp
    (eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j)))) p = _
  rw [show (Polynomial.evalRingHom t).comp
      (eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j))) =
      MvPolynomial.eval (Function.update x i t) by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, Function.update_of_ne]]

/-- **Univariate specialization at real values preserves real coefficients.** Let $p$ be a
complex multivariate polynomial with real coefficients in variables $X_j$ indexed by
$j \in \sigma$, let $i \in \sigma$, and let $a : \sigma \to \mathbb{C}$ with $a_j$ real for every
$j \ne i$. Then the univariate specialization of $p$ that keeps $X_i$ as the variable and sets
every other $X_j$ to $a_j$ has real coefficients. -/
public theorem map_star_univariateSpecialization {σ : Type*} [DecidableEq σ]
    (i : σ) (a : σ → ℂ) (p : MvPolynomial σ ℂ)
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p)
    (ha : ∀ j, j ≠ i → (starRingEnd ℂ) (a j) = a j) :
    Polynomial.map (starRingEnd ℂ) (univariateSpecialization i a p) =
      univariateSpecialization i a p := by
  let g : σ → Polynomial ℂ :=
    fun j ↦ if j = i then Polynomial.X else Polynomial.C (a j)
  have hg (j : σ) : Polynomial.map (starRingEnd ℂ) (g j) = g j := by
    by_cases hji : j = i
    · simp [g, hji]
    · simp [g, hji, ha j hji]
  change (Polynomial.mapRingHom (starRingEnd ℂ)) (eval₂Hom Polynomial.C g p) =
    eval₂Hom Polynomial.C g p
  rw [MvPolynomial.map_eval₂Hom]
  have hcomp : (Polynomial.mapRingHom (starRingEnd ℂ)).comp Polynomial.C =
      Polynomial.C.comp (starRingEnd ℂ) := by
    ext z
    simp
  rw [hcomp]
  rw [show (fun j ↦ (Polynomial.mapRingHom (starRingEnd ℂ)) (g j)) = g by
    funext j
    exact hg j]
  rw [← MvPolynomial.eval₂Hom_map_hom, hp]

end MvPolynomial

namespace MathlibExt.Algebra.MvPolynomialStable

open Filter MvPolynomial

private lemma ksRoots_im_nonpos_of_monic_limit
    (p : Polynomial ℂ) (P : ℕ → Polynomial ℂ)
    (hp : p.Monic) (hP : ∀ n, (P n).Monic)
    (hdegree : ∀ n, (P n).natDegree = p.natDegree)
    (hcoeff : ∀ k, Filter.Tendsto (fun n ↦ (P n).coeff k) Filter.atTop
      (nhds (p.coeff k)))
    (hupper : ∀ n z, z ∈ (P n).roots → z.im ≤ 0) :
    ∀ z, z ∈ p.roots → z.im ≤ 0 := by
  intro z hz
  let d := p.natDegree
  let c : ℕ → Fin d → ℂ := fun n k ↦ (P n).coeff k
  have hc_tendsto : Filter.Tendsto c Filter.atTop
      (nhds (fun k : Fin d ↦ p.coeff k)) := by
    rw [tendsto_pi_nhds]
    intro k
    exact hcoeff k
  obtain ⟨C, hCpos, hC⟩ :=
    (Metric.isBounded_range_of_tendsto c hc_tendsto).exists_pos_norm_le
  have hcauchy (n : ℕ) : (Polynomial.cauchyBound (P n) : ℝ) ≤ C + 1 := by
    rw [Polynomial.cauchyBound]
    simp only [(hP n).leadingCoeff, nnnorm_one, div_one, NNReal.coe_add, NNReal.coe_one]
    have hsup : (↑(Finset.sup (Finset.range (P n).natDegree)
        (fun k ↦ ‖(P n).coeff k‖₊)) : ℝ) ≤ C := by
      let Cnn : NNReal := ⟨C, le_of_lt hCpos⟩
      have hsup_nn : Finset.sup (Finset.range (P n).natDegree)
          (fun k ↦ ‖(P n).coeff k‖₊) ≤ Cnn := by
        apply Finset.sup_le
        intro k hk
        rw [Finset.mem_range] at hk
        let j : Fin d := ⟨k, by simpa [d, hdegree n] using hk⟩
        have hj : ‖(P n).coeff k‖ ≤ C := by
          calc
            ‖(P n).coeff k‖ = ‖c n j‖ := rfl
            _ ≤ ‖c n‖ := norm_le_pi_norm _ _
            _ ≤ C := hC (c n) ⟨n, rfl⟩
        exact_mod_cast hj
      exact_mod_cast hsup_nn
    linarith
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ (P n).roots) : ‖w‖ ≤ C + 1 := by
    have hroot := Polynomial.isRoot_of_mem_roots hw
    have hrootR : ‖w‖ < (Polynomial.cauchyBound (P n) : ℝ) := by
      exact_mod_cast hroot.norm_lt_cauchyBound (hP n).ne_zero
    exact hrootR.le.trans (hcauchy n)
  let L : ℕ → List ℂ := fun n ↦ (P n).roots.toList
  have hL (n : ℕ) : (L n).length = d := by
    dsimp [L, d]
    rw [Multiset.length_toList, ← (IsAlgClosed.splits (P n)).natDegree_eq_card_roots,
      hdegree n]
  let r : ℕ → Fin d → ℂ := fun n j ↦ (L n).get (Fin.cast (hL n).symm j)
  have hr_mem (n : ℕ) (j : Fin d) : r n j ∈ (P n).roots := by
    rw [← Multiset.mem_toList]
    exact List.get_mem _ _
  have hr_bound (n : ℕ) : ‖r n‖ ≤ C + 1 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ C + 1)]
    intro j
    exact hbound n (r n j) (hr_mem n j)
  have hr_ball (n : ℕ) : r n ∈ Metric.closedBall 0 (C + 1) := by
    exact mem_closedBall_zero_iff.mpr (hr_bound n)
  obtain ⟨rlim, hrlim, φ, hφ, hr_tendsto⟩ :=
    (isCompact_closedBall (0 : Fin d → ℂ) (C + 1)).tendsto_subseq hr_ball
  have hofFn (n : ℕ) : List.ofFn (r n) = L n := by
    apply List.ext_get
    · simp [hL n]
    · intro k hk₁ hk₂
      simp only [List.get_ofFn]
      dsimp [r]
  have heval_prod (n : ℕ) :
      (P n).eval z = ∏ j : Fin d, (z - r n j) := by
    rw [(IsAlgClosed.splits (P n)).eval_eq_prod_roots_of_monic (hP n)]
    rw [← Multiset.coe_toList (P n).roots, Multiset.map_coe, Multiset.prod_coe]
    change (List.map (fun x ↦ z - x) (L n)).prod = _
    rw [← hofFn n, List.map_ofFn, List.prod_ofFn]
    rfl
  have heval_tendsto : Filter.Tendsto (fun n ↦ (P (φ n)).eval z) Filter.atTop
      (nhds (p.eval z)) := by
    have hevalP (n : ℕ) : (P (φ n)).eval z =
        ∑ k ∈ Finset.range (d + 1), (P (φ n)).coeff k * z ^ k := by
      apply Polynomial.eval_eq_sum_range'
      dsimp [d]
      rw [hdegree]
      omega
    have hevalp : p.eval z = ∑ k ∈ Finset.range (d + 1), p.coeff k * z ^ k := by
      apply Polynomial.eval_eq_sum_range'
      dsimp [d]
      omega
    simp_rw [hevalP]
    rw [hevalp]
    apply tendsto_finsetSum
    intro k hk
    exact ((hcoeff k).comp hφ.tendsto_atTop).mul tendsto_const_nhds
  have hprod_tendsto : Filter.Tendsto
      (fun n ↦ ∏ j : Fin d, (z - r (φ n) j)) Filter.atTop
      (nhds (∏ j : Fin d, (z - rlim j))) := by
    apply tendsto_finsetProd
    intro j hj
    exact tendsto_const_nhds.sub ((tendsto_pi_nhds.mp hr_tendsto) j)
  have heval_tendsto' : Filter.Tendsto
      (fun n ↦ ∏ j : Fin d, (z - r (φ n) j)) Filter.atTop (nhds (p.eval z)) := by
    convert heval_tendsto using 1
    ext n
    exact (heval_prod (φ n)).symm
  have hp_eval : p.eval z = ∏ j : Fin d, (z - rlim j) :=
    tendsto_nhds_unique heval_tendsto' hprod_tendsto
  have hz0 : p.eval z = 0 := (Polynomial.mem_roots hp.ne_zero).mp hz
  rw [hz0] at hp_eval
  symm at hp_eval
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hp_eval
  obtain ⟨j, hj⟩ := hp_eval
  have hr_im : (rlim j).im ≤ 0 := by
    apply isClosed_Iic.mem_of_tendsto
      ((Complex.continuous_im.tendsto _).comp ((tendsto_pi_nhds.mp hr_tendsto) j))
    exact Filter.Eventually.of_forall fun n ↦
      hupper (φ n) (r (φ n) j) (hr_mem (φ n) j)
  rw [← sub_eq_zero.mp hj] at hr_im
  exact hr_im

private lemma ksTendsto_coeff_univariateSpecialization
    {σ α : Type*} [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ ℂ) (z : α → σ → ℂ) (a : σ → ℂ)
    (l : Filter α) (hz : ∀ j, Filter.Tendsto (fun n ↦ z n j) l (nhds (a j))) (k : ℕ) :
    Filter.Tendsto
      (fun n ↦ (univariateSpecialization i (z n) p).coeff k) l
      (nhds ((univariateSpecialization i a p).coeff k)) := by
  induction p using MvPolynomial.induction_on generalizing k with
  | C c => simpa [univariateSpecialization] using (tendsto_const_nhds :
      Filter.Tendsto (fun _ : α ↦ (Polynomial.C c).coeff k) l
        (nhds ((Polynomial.C c).coeff k)))
  | add p q hp hq =>
      simpa only [univariateSpecialization, map_add, Polynomial.coeff_add] using
        ((hp k).add (hq k))
  | mul_X p j hp =>
      by_cases hji : j = i
      · subst j
        cases k with
        | zero =>
            simpa [univariateSpecialization] using (tendsto_const_nhds :
              Filter.Tendsto (fun _ : α ↦ (0 : ℂ)) l (nhds 0))
        | succ k =>
            simpa [univariateSpecialization, Polynomial.coeff_mul_X] using hp k
      · simpa [univariateSpecialization, hji, Polynomial.coeff_mul_C] using
          ((hp k).mul (hz j))

private noncomputable def ksPolynomialIn {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (p : MvPolynomial σ R) :
    Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  optionEquivLeft R {j : σ // j ≠ i} (rename (Equiv.optionSubtypeNe i).symm p)

private lemma ksUnivariateSpecialization_eq_map_polynomialIn
    {σ R : Type*} [CommRing R] (i : σ) [DecidableEq σ]
    (a : σ → R) (p : MvPolynomial σ R) :
    univariateSpecialization i a p =
      Polynomial.map (eval (fun j : {j : σ // j ≠ i} ↦ a j)) (ksPolynomialIn i p) := by
  unfold univariateSpecialization ksPolynomialIn
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simpa only [map_add, Polynomial.map_add] using congrArg₂ (fun x y ↦ x + y) hp hq
  | mul_X p j hp =>
      by_cases hji : j = i
      · subst j
        simp only [map_mul]
        rw [hp]
        simp
      · simp only [map_mul]
        rw [hp]
        simp [hji]

private lemma ksTendsto_taylorCoeff_of_degree_le
    (p : Polynomial ℂ) (P : ℕ → Polynomial ℂ) (D : ℕ) (a : ℂ)
    (hdegree : ∀ n, (P n).natDegree ≤ D)
    (hcoeff : ∀ k, Tendsto (fun n ↦ (P n).coeff k) atTop (nhds (p.coeff k)))
    (k : ℕ) :
    Tendsto (fun n ↦ ((P n).taylor a).coeff k) atTop
      (nhds ((p.taylor a).coeff k)) := by
  simp only [Polynomial.taylor_coeff]
  have heval (q : Polynomial ℂ) (hq : q.natDegree ≤ D) :
      (Polynomial.hasseDeriv k q).eval a =
        ∑ j ∈ Finset.range (D + 1),
          ((j + k).choose k : ℂ) * q.coeff (j + k) * a ^ j := by
    rw [Polynomial.eval_eq_sum_range' (n := D + 1)]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Polynomial.hasseDeriv_coeff]
    · exact (Polynomial.natDegree_hasseDeriv_le _ _).trans
        (Nat.sub_le _ _ |>.trans hq) |>.trans_lt (Nat.lt_succ_self _)
  have hpdegree : p.natDegree ≤ D := by
    by_cases hp : p = 0
    · simp [hp]
    by_contra h
    have hk : D < p.natDegree := Nat.lt_of_not_ge h
    have ht := hcoeff p.natDegree
    have hzero : ∀ᶠ n in atTop, (P n).coeff p.natDegree = 0 :=
      Filter.Eventually.of_forall fun n ↦
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdegree n) hk)
    have hlimzero : Tendsto (fun n ↦ (P n).coeff p.natDegree) atTop (nhds 0) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero)
    have hpcoeff : p.coeff p.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    exact hpcoeff (tendsto_nhds_unique ht hlimzero)
  rw [heval p hpdegree]
  simp_rw [heval (P _) (hdegree _)]
  apply tendsto_finsetSum
  intro j hj
  exact ((tendsto_const_nhds.mul (hcoeff (j + k))).mul tendsto_const_nhds)

private lemma ksEventually_exists_root_norm_sub_lt
    (p : Polynomial ℂ) (P : ℕ → Polynomial ℂ) (D : ℕ)
    (hp : p ≠ 0) (hdegree : ∀ n, (P n).natDegree ≤ D)
    (hcoeff : ∀ k, Tendsto (fun n ↦ (P n).coeff k) atTop (nhds (p.coeff k)))
    {a : ℂ} (ha : p.eval a = 0) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n in atTop, ∃ z ∈ (P n).roots, ‖z - a‖ < e := by
  let q := p.taylor a
  let Q : ℕ → Polynomial ℂ := fun n ↦ (P n).taylor a
  have hq : q ≠ 0 := (Polynomial.taylor_eq_zero a p).not.mpr hp
  let k := q.natTrailingDegree
  have hqk : q.coeff k ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq
  have hQcoeff (j : ℕ) : Tendsto (fun n ↦ (Q n).coeff j) atTop
      (nhds (q.coeff j)) :=
    ksTendsto_taylorCoeff_of_degree_le p P D a hdegree hcoeff j
  have hQdegree (n : ℕ) : (Q n).natDegree ≤ D := by
    simp only [Q, Polynomial.natDegree_taylor]
    exact hdegree n
  have hQk_ne : ∀ᶠ n in atTop, (Q n).coeff k ≠ 0 :=
    (hQcoeff k).eventually_ne hqk
  have hQ_ne : ∀ᶠ n in atTop, Q n ≠ 0 := hQk_ne.mono fun n hn hzero ↦ by
    rw [hzero, Polynomial.coeff_zero] at hn
    exact hn rfl
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  push Not at hnot
  have hfreq : ∃ᶠ n in atTop,
      (∀ z ∈ (P n).roots, e ≤ ‖z - a‖) ∧ Q n ≠ 0 := hnot.and_eventually hQ_ne
  obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hQsub_ne (n : ℕ) : Q (ns n) ≠ 0 := (hbad n).2
  have hQzero_ne (n : ℕ) : (Q (ns n)).coeff 0 ≠ 0 := by
    simp only [Q, Polynomial.taylor_coeff_zero]
    intro hz
    have hroot : a ∈ (P (ns n)).roots :=
      (Polynomial.mem_roots (by
        intro hzero
        apply hQsub_ne n
        simp [Q, hzero])).mpr hz
    exact (not_lt_of_ge ((hbad n).1 a hroot)) (by simpa using he)
  let R : ℕ → Polynomial ℂ := fun n ↦
    (Q (ns n)).reverse * Polynomial.C (Q (ns n)).reverse.leadingCoeff⁻¹
  have hRmonic (n : ℕ) : (R n).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv
      (Polynomial.reverse_eq_zero.not.mpr (hQsub_ne n))
  have hRdegree (n : ℕ) : (R n).natDegree ≤ D := by
    calc
      (R n).natDegree ≤ (Q (ns n)).reverse.natDegree +
          (Polynomial.C (Q (ns n)).reverse.leadingCoeff⁻¹).natDegree := by
        exact Polynomial.natDegree_mul_le
      _ ≤ D + 0 := Nat.add_le_add
        ((Q (ns n)).reverse_natDegree_le.trans (hQdegree (ns n))) (by simp)
      _ = D := by simp
  have hRroots (n : ℕ) (z : ℂ) (hz : z ∈ (R n).roots) : ‖z‖ ≤ e⁻¹ := by
    have hlc0 : (Q (ns n)).reverse.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.reverse_eq_zero.not.mpr (hQsub_ne n))
    have hlc : (Q (ns n)).reverse.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc0
    have hzrev : z ∈ (Q (ns n)).reverse.roots := by
      simp only [R] at hz
      rw [mul_comm, Polynomial.roots_C_mul _ hlc] at hz
      exact hz
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      have hzero : (Q (ns n)).reverse.eval 0 = 0 :=
        (Polynomial.mem_roots
          (Polynomial.reverse_eq_zero.not.mpr (hQsub_ne n))).mp hzrev
      have hcoeff : (Q (ns n)).reverse.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hzero
      rw [Polynomial.coeff_zero_reverse] at hcoeff
      exact Polynomial.leadingCoeff_ne_zero.mpr (hQsub_ne n) hcoeff
    have hzinvQ : (Q (ns n)).eval z⁻¹ = 0 := by
      have hrevzero : (Q (ns n)).reverse.eval z = 0 :=
        (Polynomial.mem_roots
          (Polynomial.reverse_eq_zero.not.mpr (hQsub_ne n))).mp hzrev
      let hinv : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
      have h := (@Polynomial.eval₂_reverse_eq_zero_iff ℂ _ ℂ _
        (RingHom.id ℂ) z⁻¹ hinv (Q (ns n))).mp
      apply h
      rw [Polynomial.eval₂_eq_eval_map]
      simpa only [Polynomial.map_id, invOf_eq_inv, inv_inv] using hrevzero
    have hzinvP : (P (ns n)).eval (z⁻¹ + a) = 0 := by
      simpa [Q, Polynomial.taylor_eval] using hzinvQ
    have hroot : z⁻¹ + a ∈ (P (ns n)).roots :=
      (Polynomial.mem_roots (by
        intro hzero
        apply hQsub_ne n
        simp [Q, hzero])).mpr hzinvP
    have hfar := (hbad n).1 (z⁻¹ + a) hroot
    have hinv : e ≤ ‖z‖⁻¹ := by
      simpa [add_sub_cancel_right] using hfar
    exact (le_inv_comm₀ he (norm_pos_iff.mpr hz0)).mp hinv
  let C : ℝ := max e⁻¹ 1 ^ D * (D.choose (D / 2) : ℝ)
  have hRcoeff (n j : ℕ) : ‖(R n).coeff j‖ ≤ C := by
    simpa [C] using Polynomial.coeff_bdd_of_roots_le (RingHom.id ℂ)
      (hRmonic n) (by simpa using IsAlgClosed.splits (R n)) (hRdegree n)
      (by simpa using hRroots n) j
  have hbound (n : ℕ) : ‖(Q (ns n)).coeff k‖ ≤
      ‖(Q (ns n)).coeff 0‖ * C := by
    by_cases hkdeg : k ≤ (Q (ns n)).natDegree
    · let j := (Q (ns n)).natDegree - k
      have hrevcoeff : (Q (ns n)).reverse.coeff j = (Q (ns n)).coeff k := by
        rw [Polynomial.coeff_reverse, Polynomial.revAt_le]
        · simp [j, Nat.sub_sub_self hkdeg]
        · exact Nat.sub_le _ _
      have hlc : (Q (ns n)).reverse.leadingCoeff = (Q (ns n)).coeff 0 := by
        rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
          (Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hQzero_ne n)))]
      have hcoeffR : (R n).coeff j =
          (Q (ns n)).coeff k * ((Q (ns n)).coeff 0)⁻¹ := by
        simp only [R, Polynomial.coeff_mul_C, hlc, hrevcoeff]
      have heq : ‖(Q (ns n)).coeff k‖ =
          ‖(Q (ns n)).coeff 0‖ * ‖(R n).coeff j‖ := by
        rw [hcoeffR, norm_mul, norm_inv]
        calc
          ‖(Q (ns n)).coeff k‖ = ‖(Q (ns n)).coeff k‖ *
              ‖(Q (ns n)).coeff 0‖ / ‖(Q (ns n)).coeff 0‖ :=
            (mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr (hQzero_ne n))).symm
          _ = ‖(Q (ns n)).coeff 0‖ *
              (‖(Q (ns n)).coeff k‖ * ‖(Q (ns n)).coeff 0‖⁻¹) := by
            rw [div_eq_mul_inv]
            ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hRcoeff n j) (norm_nonneg _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hkdeg),
        norm_zero]
      positivity
  have hleft : Tendsto (fun n ↦ ‖(Q (ns n)).coeff k‖) atTop
      (nhds ‖q.coeff k‖) := ((hQcoeff k).comp hns).norm
  have hright : Tendsto (fun n ↦ ‖(Q (ns n)).coeff 0‖ * C) atTop (nhds 0) := by
    have hqzero : q.coeff 0 = 0 := by simpa [q, Polynomial.taylor_coeff_zero]
    simpa [hqzero] using (((hQcoeff 0).comp hns).norm.mul_const C)
  have hnormle : ‖q.coeff k‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hbound)
  exact hqk (norm_eq_zero.mp (hnormle.antisymm (norm_nonneg _)))

/-- Specializing all but one variable of a stable polynomial to the closed upper half-plane
leaves every root of a nonzero specialization in the closed lower half-plane. -/
public theorem _root_.MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization
    {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℂ} (hp : p.IsStable)
    (i : σ) (a : σ → ℂ) (ha : ∀ j, j ≠ i → 0 ≤ (a j).im)
    (hq : univariateSpecialization i a p ≠ 0) :
    ∀ w ∈ (univariateSpecialization i a p).roots, w.im ≤ 0 := by
  let δ : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1)
  let z : ℕ → σ → ℂ := fun n j ↦ if j = i then a j else a j + δ n * Complex.I
  have hδ : Tendsto δ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz (j : σ) : Tendsto (fun n ↦ z n j) atTop (nhds (a j)) := by
    by_cases hji : j = i
    · simp [z, hji]
    · simpa [z, hji] using tendsto_const_nhds.add (hδ.mul_const Complex.I)
  let q := univariateSpecialization i a p
  let P : ℕ → Polynomial ℂ := fun n ↦ univariateSpecialization i (z n) p
  have hdegree (n : ℕ) : (P n).natDegree ≤ p.degreeOf i := by
    rw [show P n = univariateSpecialization i (z n) p by rfl,
      ksUnivariateSpecialization_eq_map_polynomialIn]
    exact Polynomial.natDegree_map_le.trans_eq (degreeOf_eq_natDegree i p).symm
  have hcoeff (k : ℕ) : Tendsto (fun n ↦ (P n).coeff k) atTop
      (nhds (q.coeff k)) :=
    ksTendsto_coeff_univariateSpecialization i p z a atTop hz k
  have hupper (n : ℕ) (w : ℂ) (hw : w ∈ (P n).roots) : w.im ≤ 0 := by
    by_contra hn
    have hwpos : 0 < w.im := lt_of_not_ge hn
    have hall (j : σ) : 0 < (Function.update (z n) i w j).im := by
      by_cases hji : j = i
      · subst j
        simpa using hwpos
      · rw [Function.update_of_ne hji]
        have hδpos : 0 < (δ n).re := by
          dsimp [δ]
          rw [one_div, Complex.inv_re]
          norm_num [Complex.normSq]
          positivity
        simp only [z, hji, ↓reduceIte, Complex.add_im, Complex.mul_im, Complex.I_im,
          Complex.I_re, mul_one, mul_zero]
        linarith [ha j hji]
    have hnonzero := hp (Function.update (z n) i w) hall
    have hroot : (P n).eval w = 0 :=
      Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hw)
    rw [show (P n).eval w = MvPolynomial.eval (Function.update (z n) i w) p by
      exact eval_univariateSpecialization i (z n) w p] at hroot
    exact hnonzero hroot
  intro w hw
  by_contra hn
  have hwpos : 0 < w.im := lt_of_not_ge hn
  let e := w.im / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hwzero : q.eval w = 0 := (Polynomial.mem_roots hq).mp hw
  obtain ⟨n, v, hvroot, hvclose⟩ :=
    (ksEventually_exists_root_norm_sub_lt q P (p.degreeOf i) hq hdegree hcoeff
      hwzero he).exists
  have hvupper : v.im ≤ 0 := hupper n v hvroot
  have himdist : |v.im - w.im| ≤ ‖v - w‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (v - w)
  have hwle : w.im ≤ |v.im - w.im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  dsimp [e] at hvclose
  linarith

private lemma ksRoots_im_nonpos_univariateSpecialization
    {σ : Type*} [DecidableEq σ] (i : σ) (p : MvPolynomial σ ℂ)
    (hp : p.IsStable) (d : ℕ)
    (hmonic : ∀ x, (univariateSpecialization i x p).Monic)
    (hdegree : ∀ x, (univariateSpecialization i x p).natDegree = d)
    (a : σ → ℂ) (ha : ∀ j, j ≠ i → 0 ≤ (a j).im) :
    ∀ w ∈ (univariateSpecialization i a p).roots, w.im ≤ 0 := by
  let δ : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1)
  let z : ℕ → σ → ℂ := fun n j ↦ if j = i then a j else a j + δ n * Complex.I
  have hδ : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hz (j : σ) : Filter.Tendsto (fun n ↦ z n j) Filter.atTop (nhds (a j)) := by
    by_cases hji : j = i
    · simp [z, hji]
    · simpa [z, hji] using tendsto_const_nhds.add (hδ.mul_const Complex.I)
  let q := univariateSpecialization i a p
  let P : ℕ → Polynomial ℂ := fun n ↦ univariateSpecialization i (z n) p
  have hqmonic : q.Monic := hmonic a
  have hPmonic (n : ℕ) : (P n).Monic := hmonic (z n)
  have hPdegree (n : ℕ) : (P n).natDegree = q.natDegree := by
    rw [show (P n).natDegree = d by exact hdegree (z n),
      show q.natDegree = d by exact hdegree a]
  have hcoeff (k : ℕ) : Filter.Tendsto (fun n ↦ (P n).coeff k) Filter.atTop
      (nhds (q.coeff k)) :=
    ksTendsto_coeff_univariateSpecialization i p z a Filter.atTop hz k
  have hupper (n : ℕ) (w : ℂ) (hw : w ∈ (P n).roots) : w.im ≤ 0 := by
    by_contra hn
    have hwpos : 0 < w.im := lt_of_not_ge hn
    have hall (j : σ) : 0 < (Function.update (z n) i w j).im := by
      by_cases hji : j = i
      · subst j
        simpa using hwpos
      · rw [Function.update_of_ne hji]
        have hδpos : 0 < (δ n).re := by
          dsimp [δ]
          rw [one_div, Complex.inv_re]
          norm_num [Complex.normSq]
          positivity
        simp only [z, hji, ↓reduceIte, Complex.add_im, Complex.mul_im, Complex.I_im,
          Complex.I_re, mul_one, mul_zero]
        linarith [ha j hji]
    have hnonzero := hp (Function.update (z n) i w) hall
    have hroot : (P n).eval w = 0 :=
      Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hw)
    rw [show (P n).eval w = MvPolynomial.eval (Function.update (z n) i w) p by
      exact eval_univariateSpecialization i (z n) w p] at hroot
    exact hnonzero hroot
  exact ksRoots_im_nonpos_of_monic_limit q P hqmonic hPmonic hPdegree hcoeff hupper

/-- A real-stable polynomial is real-rooted after specializing every variable but one to real
values, provided the resulting univariate degree is constant. -/
public theorem _root_.MvPolynomial.isRealRooted_univariateSpecialization_of_isRealStable
    {σ : Type*} [DecidableEq σ] (i : σ) (p : MvPolynomial σ ℂ)
    (hp : p.IsRealStable) (d : ℕ)
    (hmonic : ∀ x, (univariateSpecialization i x p).Monic)
    (hdegree : ∀ x, (univariateSpecialization i x p).natDegree = d)
    (a : σ → ℂ) (ha : ∀ j, j ≠ i → (a j).im = 0) :
    (univariateSpecialization i a p).IsRealRooted := by
  let q := univariateSpecialization i a p
  have hupper : ∀ z ∈ q.roots, z.im ≤ 0 :=
    ksRoots_im_nonpos_univariateSpecialization i p hp.2 d hmonic hdegree a
      (fun j hji ↦ (ha j hji).ge)
  have hfixed (j : σ) (hji : j ≠ i) : (starRingEnd ℂ) (a j) = a j := by
    apply Complex.ext <;> simp [ha j hji]
  have hreal : Polynomial.map (starRingEnd ℂ) q = q :=
    MvPolynomial.map_star_univariateSpecialization i a p hp.1 hfixed
  exact Polynomial.isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
    q (hmonic a).ne_zero hreal hupper

private lemma ksInv_im_neg_of_im_pos (z : ℂ) (hz : 0 < z.im) : z⁻¹.im < 0 := by
  rw [Complex.inv_im]
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hz) (Complex.normSq_pos.mpr hz0)

private lemma ksIm_sum_inv_sub_neg (w : ℂ) (hw : 0 < w.im) (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z.im ≤ 0) (hs0 : s ≠ 0) :
    ((s.map fun z ↦ 1 / (w - z)).sum).im < 0 := by
  induction s using Multiset.induction_on with
  | empty => exact (hs0 rfl).elim
  | cons a s ih =>
      have ha_im : 0 < (w - a).im := by
        rw [Complex.sub_im]
        linarith [hs a (by simp)]
      have ha : (1 / (w - a)).im < 0 := by
        simpa only [one_div] using ksInv_im_neg_of_im_pos (w - a) ha_im
      rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
      by_cases htail : s = 0
      · subst s
        simpa using ha
      · have htail_im : ((s.map fun z ↦ 1 / (w - z)).sum).im < 0 := by
          apply ih
          · intro z hz
            exact hs z (by simp [hz])
          · exact htail
        linarith

private lemma ksEval_sub_derivative_ne_zero (p : Polynomial ℂ) (w : ℂ)
    (hw : 0 < w.im) (hpw : p.eval w ≠ 0)
    (hroots : ∀ z ∈ p.roots, z.im ≤ 0) :
    (p - p.derivative).eval w ≠ 0 := by
  intro hzero
  have hder : p.derivative.eval w = p.eval w := by
    rw [Polynomial.eval_sub, sub_eq_zero] at hzero
    exact hzero.symm
  have hlog := (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpw
  have hsum : (p.roots.map fun z ↦ 1 / (w - z)).sum = 1 := by
    rw [← hlog, hder]
    exact div_self hpw
  by_cases hroots0 : p.roots = 0
  · rw [hroots0] at hsum
    simp at hsum
  · have hneg := ksIm_sum_inv_sub_neg w hw p.roots hroots hroots0
    have him := congrArg Complex.im hsum
    rw [Complex.one_im] at him
    linarith

/-- The operator `1 - ∂ᵢ` preserves stability. -/
public theorem _root_.MvPolynomial.IsStable.sub_pderiv {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : p.IsStable) (i : σ) :
    (p - pderiv i p).IsStable := by
  classical
  intro z hz
  let q : Polynomial ℂ := univariateSpecialization i z p
  have hqz : q.eval (z i) ≠ 0 := by
    have hpz := hp z hz
    simpa [q, eval_univariateSpecialization] using hpz
  have hroots : ∀ a ∈ q.roots, a.im ≤ 0 := by
    intro a ha
    by_contra hnot
    have ha_pos : 0 < a.im := lt_of_not_ge hnot
    have hupper : ∀ j, 0 < (Function.update z i a j).im := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ha_pos
      · simpa [Function.update_of_ne hji] using hz j
    have hnonzero := hp (Function.update z i a) hupper
    have hroot : q.eval a = 0 :=
      Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots ha)
    rw [show q.eval a = MvPolynomial.eval (Function.update z i a) p by
      exact eval_univariateSpecialization i z a p] at hroot
    exact hnonzero hroot
  have hne := ksEval_sub_derivative_ne_zero q (z i) (hz i) hqz hroots
  have hpoly : univariateSpecialization i z (p - pderiv i p) = q - q.derivative := by
    calc
      univariateSpecialization i z (p - pderiv i p) =
          univariateSpecialization i z p - univariateSpecialization i z (pderiv i p) := by
        exact map_sub (eval₂Hom Polynomial.C
          (fun j ↦ if j = i then Polynomial.X else Polynomial.C (z j))) p (pderiv i p)
      _ = q - q.derivative := by rw [derivative_univariateSpecialization]
  have heval := eval_univariateSpecialization i z (z i) (p - pderiv i p)
  rw [hpoly] at heval
  intro hzero
  apply hne
  rw [heval]
  simpa using hzero

/-- The operator `1 - ∂ᵢ` preserves real stability. -/
public theorem _root_.MvPolynomial.IsRealStable.sub_pderiv {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : p.IsRealStable) (i : σ) :
    (p - pderiv i p).IsRealStable := by
  constructor
  · rw [map_sub, ← MvPolynomial.pderiv_map, hp.1]
  · exact MvPolynomial.IsStable.sub_pderiv hp.2 i

/-- Any finite composition of the operators `1 - ∂ᵢ` preserves stability. -/
public theorem _root_.MvPolynomial.IsStable.mixedDifferential {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : p.IsStable) (indices : List σ) :
    (MvPolynomial.mixedDifferential indices p).IsStable := by
  induction indices generalizing p with
  | nil => simpa using hp
  | cons i is ih =>
      rw [MvPolynomial.mixedDifferential_cons]
      exact ih (MvPolynomial.IsStable.sub_pderiv hp i)

/-- Any finite composition of the operators `1 - ∂ᵢ` preserves real stability. -/
public theorem _root_.MvPolynomial.IsRealStable.mixedDifferential {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : p.IsRealStable) (indices : List σ) :
    (MvPolynomial.mixedDifferential indices p).IsRealStable := by
  induction indices generalizing p with
  | nil => simpa using hp
  | cons i is ih =>
      rw [MvPolynomial.mixedDifferential_cons]
      exact ih (MvPolynomial.IsRealStable.sub_pderiv hp i)

end MathlibExt.Algebra.MvPolynomialStable
