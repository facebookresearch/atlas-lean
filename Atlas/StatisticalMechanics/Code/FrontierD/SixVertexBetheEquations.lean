/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBlockRepetition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexDelta (c : ℝ) : ℝ := (2 - c ^ 2) / 2

theorem sixVertexDelta_lt_neg_one {c : ℝ} (hc : 2 < c) :
    sixVertexDelta c < -1 := by
  unfold sixVertexDelta
  nlinarith


def sixVertexThetaDenominator (c x y : ℝ) : ℝ :=
  Real.cos x + Real.cos y - 2 * sixVertexDelta c

theorem sixVertexThetaDenominator_pos {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    0 < sixVertexThetaDenominator c x y := by
  have hx := Real.neg_one_le_cos x
  have hy := Real.neg_one_le_cos y
  have hdelta := sixVertexDelta_lt_neg_one hc
  unfold sixVertexThetaDenominator
  linarith


noncomputable def sixVertexTheta (c x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan
    ((Real.sin x - Real.sin y) / sixVertexThetaDenominator c x y)

@[simp] theorem sixVertexTheta_self (c x : ℝ) :
    sixVertexTheta c x x = 0 := by
  simp [sixVertexTheta]

theorem sixVertexTheta_antisymm (c x y : ℝ) :
    sixVertexTheta c y x = -sixVertexTheta c x y := by
  have hden : sixVertexThetaDenominator c y x =
      sixVertexThetaDenominator c x y := by
    unfold sixVertexThetaDenominator
    ring
  unfold sixVertexTheta
  rw [hden]
  have hratio :
      (Real.sin y - Real.sin x) / sixVertexThetaDenominator c x y =
        -((Real.sin x - Real.sin y) /
          sixVertexThetaDenominator c x y) := by ring
  rw [hratio, Real.arctan_neg]
  ring_nf

theorem sixVertexTheta_neg (c x y : ℝ) :
    sixVertexTheta c (-x) (-y) = -sixVertexTheta c x y := by
  unfold sixVertexTheta sixVertexThetaDenominator
  simp only [Real.sin_neg, Real.cos_neg]
  have hratio :
      (-Real.sin x - -Real.sin y) /
          (Real.cos x + Real.cos y - 2 * sixVertexDelta c) =
        -((Real.sin x - Real.sin y) /
          (Real.cos x + Real.cos y - 2 * sixVertexDelta c)) := by ring
  rw [hratio, Real.arctan_neg]
  ring

theorem sixVertexTheta_add_two_pi_left (c x y : ℝ) :
    sixVertexTheta c (x + 2 * Real.pi) y =
      sixVertexTheta c x y - 2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

theorem sixVertexTheta_add_two_pi_right (c x y : ℝ) :
    sixVertexTheta c x (y + 2 * Real.pi) =
      sixVertexTheta c x y + 2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

theorem sixVertexTheta_pi_pair (c y : ℝ) :
    sixVertexTheta c Real.pi y + sixVertexTheta c Real.pi (-y) =
      -2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_neg, Real.cos_neg,
    zero_sub]
  have hratio :
      (-Real.sin y) / (-1 + Real.cos y - 2 * sixVertexDelta c) =
        -(Real.sin y / (-1 + Real.cos y - 2 * sixVertexDelta c)) := by ring
  rw [hratio, Real.arctan_neg]
  ring_nf

theorem sixVertexTheta_neg_pi_pair (c y : ℝ) :
    sixVertexTheta c (-Real.pi) y + sixVertexTheta c (-Real.pi) (-y) =
      2 * Real.pi := by
  have h1 := sixVertexTheta_neg c Real.pi (-y)
  have h2 := sixVertexTheta_neg c Real.pi y
  have hpi := sixVertexTheta_pi_pair c y
  simp only [neg_neg] at h1
  linarith

theorem continuous_sixVertexTheta {c : ℝ} (hc : 2 < c) :
    Continuous fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2 := by
  have hden : ∀ xy : ℝ × ℝ,
      sixVertexThetaDenominator c xy.1 xy.2 ≠ 0 :=
    fun xy => (sixVertexThetaDenominator_pos hc xy.1 xy.2).ne'
  unfold sixVertexTheta
  apply (continuous_snd.sub continuous_fst).add
  apply continuous_const.mul
  apply Real.continuous_arctan.comp
  apply Continuous.div
  · fun_prop
  · unfold sixVertexThetaDenominator
    fun_prop
  · exact hden


theorem hasDerivAt_sixVertexTheta_left {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasDerivAt (fun t => sixVertexTheta c t y)
      (4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (sixVertexThetaDenominator c x y ^ 2 +
          (Real.sin x - Real.sin y) ^ 2)) x := by
  let a := sixVertexThetaDenominator c x y
  let b := Real.sin x - Real.sin y
  have ha : a ≠ 0 := (sixVertexThetaDenominator_pos hc x y).ne'
  have hnum : HasDerivAt (fun t => Real.sin t - Real.sin y)
      (Real.cos x) x := Real.hasDerivAt_sin x |>.sub_const _
  have hden : HasDerivAt
      (fun t => Real.cos t + Real.cos y - 2 * sixVertexDelta c)
      (-Real.sin x) x :=
    (Real.hasDerivAt_cos x).add_const _ |>.sub_const _
  have hratio := hnum.div hden ha
  have harctan := hratio.arctan
  have htheta := ((hasDerivAt_const x y).sub (hasDerivAt_id x)).add
    (HasDerivAt.const_mul 2 harctan)
  convert htheta using 1
  dsimp only
  change
    4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (a ^ 2 + b ^ 2) =
      (0 - 1) + 2 *
        (1 / (1 + ((Real.sin x - Real.sin y) / a) ^ 2) *
          ((Real.cos x * a -
            (Real.sin x - Real.sin y) * -Real.sin x) / a ^ 2))
  field_simp
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  dsimp [a, b, sixVertexThetaDenominator]
  nlinarith

theorem sixVertexTheta_left_deriv_neg {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (sixVertexThetaDenominator c x y ^ 2 +
          (Real.sin x - Real.sin y) ^ 2) < 0 := by
  have hdelta := sixVertexDelta_lt_neg_one hc
  have hcos := Real.neg_one_le_cos y
  have hden := sixVertexThetaDenominator_pos hc x y
  have hcy : 0 < Real.cos y - sixVertexDelta c := by linarith
  have hfour : 4 * sixVertexDelta c < 0 := by nlinarith
  have hsq : 0 < sixVertexThetaDenominator c x y ^ 2 +
      (Real.sin x - Real.sin y) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfour hcy) hsq

theorem strictAnti_sixVertexTheta_left {c : ℝ} (hc : 2 < c) (y : ℝ) :
    StrictAnti fun x => sixVertexTheta c x y := by
  apply strictAnti_of_deriv_neg
  intro x
  rw [(hasDerivAt_sixVertexTheta_left hc x y).deriv]
  exact sixVertexTheta_left_deriv_neg hc x y

theorem strictMono_sixVertexTheta_right {c : ℝ} (hc : 2 < c) (x : ℝ) :
    StrictMono fun y => sixVertexTheta c x y := by
  intro y z hyz
  have h := strictAnti_sixVertexTheta_left hc x hyz
  have hneg := neg_lt_neg h
  change -sixVertexTheta c y x < -sixVertexTheta c z x at hneg
  rw [← sixVertexTheta_antisymm c y x,
    ← sixVertexTheta_antisymm c z x] at hneg
  exact hneg


def sixVertexCentralQuantumNumber {n : ℕ} (j : Fin n) : ℝ :=
  ((j.val : ℝ) - (j.rev.val : ℝ)) / 2

theorem sixVertexCentralQuantumNumber_rev {n : ℕ} (j : Fin n) :
    sixVertexCentralQuantumNumber j.rev =
      -sixVertexCentralQuantumNumber j := by
  simp [sixVertexCentralQuantumNumber]
  ring

theorem sixVertexCentralQuantumNumber_eq {n : ℕ} (j : Fin n) :
    sixVertexCentralQuantumNumber j =
      (j.val : ℝ) - ((n : ℝ) - 1) / 2 := by
  simp [sixVertexCentralQuantumNumber]
  ring

theorem sum_sixVertexCentralQuantumNumber (n : ℕ) :
    ∑ j : Fin n, sixVertexCentralQuantumNumber j = 0 := by
  have hrev : (∑ j : Fin n, (j.rev.val : ℝ)) = ∑ j : Fin n, (j.val : ℝ) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro j
    rfl
  unfold sixVertexCentralQuantumNumber
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hrev, sub_self, zero_div]

theorem strictMono_sixVertexCentralQuantumNumber (n : ℕ) :
    StrictMono (sixVertexCentralQuantumNumber : Fin n → ℝ) := by
  intro j k hjk
  rw [sixVertexCentralQuantumNumber_eq,
    sixVertexCentralQuantumNumber_eq]
  have hval : (j.val : ℝ) < k.val := by exact_mod_cast hjk
  linarith


def SixVertexSatisfiesBetheEquations
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Prop :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ k, sixVertexTheta c (p j) (p k)



noncomputable def sixVertexBetheUpdate
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j -
    ∑ k, sixVertexTheta c (p j) (p k)) / N


def SixVertexRootSymmetric {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ j, p j.rev = -p j

theorem SixVertexRootSymmetric.reverse_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexRootSymmetric p) :
    (fun j => -p j.rev) = p := by
  funext j
  rw [hp]
  simp

theorem sum_sixVertexTheta_pi_of_symmetric (c : ℝ)
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexRootSymmetric p) :
    ∑ k, sixVertexTheta c Real.pi (p k) = -(n : ℝ) * Real.pi := by
  let S := ∑ k, sixVertexTheta c Real.pi (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c Real.pi (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair :
      S + S = ∑ k, (sixVertexTheta c Real.pi (p k) +
        sixVertexTheta c Real.pi (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c Real.pi (p k.rev) := by rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c Real.pi (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
      _ = _ := Finset.sum_add_distrib.symm
  have heval :
      (∑ k : Fin n, (sixVertexTheta c Real.pi (p k) +
        sixVertexTheta c Real.pi (-p k))) = -(2 * n : ℝ) * Real.pi := by
    simp_rw [sixVertexTheta_pi_pair]
    simp
    ring
  rw [heval] at hpair
  dsimp [S] at hpair ⊢
  linarith

theorem sum_sixVertexTheta_neg_pi_of_symmetric (c : ℝ)
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexRootSymmetric p) :
    ∑ k, sixVertexTheta c (-Real.pi) (p k) = (n : ℝ) * Real.pi := by
  let S := ∑ k, sixVertexTheta c (-Real.pi) (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c (-Real.pi) (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair :
      S + S = ∑ k, (sixVertexTheta c (-Real.pi) (p k) +
        sixVertexTheta c (-Real.pi) (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c (-Real.pi) (p k.rev) := by rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c (-Real.pi) (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hp]
      _ = _ := Finset.sum_add_distrib.symm
  have heval :
      (∑ k : Fin n, (sixVertexTheta c (-Real.pi) (p k) +
        sixVertexTheta c (-Real.pi) (-p k))) = (2 * n : ℝ) * Real.pi := by
    simp_rw [sixVertexTheta_neg_pi_pair]
    simp
    ring
  rw [heval] at hpair
  dsimp [S] at hpair ⊢
  linarith

theorem sixVertexBetheUpdate_eq_self_iff
    {c : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ) :
    sixVertexBetheUpdate c N n p = p ↔
      SixVertexSatisfiesBetheEquations c N n p := by
  constructor
  · intro h j
    have hj := congrFun h j
    unfold sixVertexBetheUpdate at hj
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hN0] at hj
    linarith
  · intro hp
    funext j
    unfold sixVertexBetheUpdate
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hN0]
    linarith [hp j]

theorem continuous_sixVertexBetheUpdate {c : ℝ} (hc : 2 < c)
    (N n : ℕ) :
    Continuous fun p : Fin n → ℝ => sixVertexBetheUpdate c N n p := by
  apply continuous_pi
  intro j
  unfold sixVertexBetheUpdate
  apply Continuous.div_const
  apply Continuous.sub continuous_const
  change Continuous fun p : Fin n → ℝ =>
    ∑ k ∈ Finset.univ, sixVertexTheta c (p j) (p k)
  apply continuous_finsetSum
  intro k _
  have hj : Continuous fun p : Fin n → ℝ => p j := continuous_apply j
  have hk : Continuous fun p : Fin n → ℝ => p k := continuous_apply k
  exact (continuous_sixVertexTheta hc).comp (hj.prodMk hk)

theorem sixVertexBetheUpdate_reverse_neg
    (c : ℝ) {N n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    sixVertexBetheUpdate c N n (fun k => -p k.rev) j =
      -sixVertexBetheUpdate c N n p j.rev := by
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k.rev)) =
        ∑ k : Fin n, sixVertexTheta c (p j.rev) (p k) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  unfold sixVertexBetheUpdate
  rw [sixVertexCentralQuantumNumber_rev]
  simp only [sixVertexTheta_neg, Finset.sum_neg_distrib, hsum]
  ring

theorem sixVertexBetheUpdate_symmetric
    (c : ℝ) {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexRootSymmetric p) :
    SixVertexRootSymmetric (sixVertexBetheUpdate c N n p) := by
  intro j
  have hrev := sixVertexBetheUpdate_reverse_neg c (N := N) p j
  rw [hp.reverse_neg] at hrev
  linarith


def SixVertexRootsInOpenInterval {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ j, -Real.pi < p j ∧ p j < Real.pi

theorem sixVertexBetheUpdate_mem_openInterval {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hhalf : 2 * n ≤ N) {p : Fin n → ℝ}
    (hsymm : SixVertexRootSymmetric p)
    (hinterval : SixVertexRootsInOpenInterval p) :
    SixVertexRootsInOpenInterval (sixVertexBetheUpdate c N n p) := by
  intro j
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsumPi := sum_sixVertexTheta_pi_of_symmetric c hsymm
  have hsumNegPi := sum_sixVertexTheta_neg_pi_of_symmetric c hsymm
  have hsumUpper :
      (∑ k, sixVertexTheta c Real.pi (p k)) <
        ∑ k, sixVertexTheta c (p j) (p k) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k) (hinterval j).2).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) (hinterval j).2⟩
  have hsumLower :
      (∑ k, sixVertexTheta c (p j) (p k)) <
        ∑ k, sixVertexTheta c (-Real.pi) (p k) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k) (hinterval j).1).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) (hinterval j).1⟩
  have hjupper : (j.val : ℝ) ≤ (n : ℝ) - 1 := by
    have hjlt : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hjint : (j.val : ℤ) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjint
    linarith
  have hjlower : (0 : ℝ) ≤ j.val := by positivity
  have hIupper : sixVertexCentralQuantumNumber j ≤ ((n : ℝ) - 1) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    linarith
  have hIlower : -((n : ℝ) - 1) / 2 ≤ sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq]
    linarith
  have hhalfre : (2 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhalf
  have hnre : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcount : (2 : ℝ) * (n : ℝ) - 1 < (N : ℝ) := by linarith
  unfold sixVertexBetheUpdate
  constructor
  · apply (lt_div_iff₀ hNreal).mpr
    rw [hsumNegPi] at hsumLower
    nlinarith [Real.pi_pos]
  · apply (div_lt_iff₀ hNreal).mpr
    rw [hsumPi] at hsumUpper
    nlinarith [Real.pi_pos]


theorem sixVertexBetheUpdate_strictMono {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ} (hp : StrictMono p) :
    StrictMono (sixVertexBetheUpdate c N n p) := by
  intro j k hjk
  have hpjk : p j < p k := hp hjk
  have htheta :
      (∑ l, sixVertexTheta c (p k) (p l)) <
        ∑ l, sixVertexTheta c (p j) (p l) := by
    apply Finset.sum_lt_sum
    · intro l _
      exact (strictAnti_sixVertexTheta_left hc (p l) hpjk).le
    · exact ⟨j, Finset.mem_univ _,
        strictAnti_sixVertexTheta_left hc (p j) hpjk⟩
  have hquantum := strictMono_sixVertexCentralQuantumNumber n hjk
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sixVertexBetheUpdate
  apply div_lt_div_of_pos_right _ hNreal
  nlinarith [Real.pi_pos]

theorem sixVertexBetheUpdate_strictMono_of_monotone {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ} (hp : Monotone p) :
    StrictMono (sixVertexBetheUpdate c N n p) := by
  intro j k hjk
  have hpjk : p j ≤ p k := hp hjk.le
  have htheta :
      (∑ l, sixVertexTheta c (p k) (p l)) ≤
        ∑ l, sixVertexTheta c (p j) (p l) := by
    apply Finset.sum_le_sum
    intro l _
    exact (strictAnti_sixVertexTheta_left hc (p l)).antitone hpjk
  have hquantum := strictMono_sixVertexCentralQuantumNumber n hjk
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sixVertexBetheUpdate
  apply div_lt_div_of_pos_right _ hNreal
  nlinarith [Real.pi_pos]


def SixVertexClosedRootSimplex {n : ℕ} (p : Fin n → ℝ) : Prop :=
  Monotone p ∧ SixVertexRootSymmetric p ∧
    ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi



def SixVertexOpenRootSimplex {n : ℕ} (p : Fin n → ℝ) : Prop :=
  StrictMono p ∧ SixVertexRootSymmetric p ∧
    SixVertexRootsInOpenInterval p

theorem sixVertexClosedRootSimplex_nonempty (n : ℕ) :
    Set.Nonempty {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  refine ⟨fun _ => 0, ?_⟩
  constructor
  · exact fun _ _ _ => le_rfl
  constructor
  · intro j
    simp
  · intro j
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).le, Real.pi_pos.le⟩

theorem convex_sixVertexClosedRootSimplex (n : ℕ) :
    Convex ℝ {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpmono, hpsymm, hpint⟩
  rcases hq with ⟨hqmono, hqsymm, hqint⟩
  constructor
  · intro i j hij
    change a * p i + b * q i ≤ a * p j + b * q j
    exact add_le_add (mul_le_mul_of_nonneg_left (hpmono hij) ha)
      (mul_le_mul_of_nonneg_left (hqmono hij) hb)
  constructor
  · intro j
    change a * p j.rev + b * q j.rev = -(a * p j + b * q j)
    rw [hpsymm, hqsymm]
    ring
  · intro j
    change -Real.pi ≤ a * p j + b * q j ∧
      a * p j + b * q j ≤ Real.pi
    constructor <;> nlinarith [(hpint j).1, (hpint j).2,
      (hqint j).1, (hqint j).2]

theorem isClosed_sixVertexClosedRootSimplex (n : ℕ) :
    IsClosed {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  have hmono : IsClosed {p : Fin n → ℝ | Monotone p} := isClosed_monotone
  have hsymm : IsClosed {p : Fin n → ℝ | SixVertexRootSymmetric p} := by
    have heq : {p : Fin n → ℝ | SixVertexRootSymmetric p} =
        ⋂ j, {p | p j.rev = -p j} := by
      ext p
      simp [SixVertexRootSymmetric]
    rw [heq]
    apply isClosed_iInter
    intro j
    exact isClosed_eq (continuous_apply j.rev) (continuous_apply j).neg
  have hinterval : IsClosed {p : Fin n → ℝ |
      ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi} := by
    have heq : {p : Fin n → ℝ | ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi} =
        ⋂ j, ({p | -Real.pi ≤ p j} ∩ {p | p j ≤ Real.pi}) := by
      ext p
      simp
    rw [heq]
    apply isClosed_iInter
    intro j
    exact (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)
  simpa only [SixVertexClosedRootSimplex, Set.setOf_and] using
    hmono.inter (hsymm.inter hinterval)

theorem isCompact_sixVertexClosedRootSimplex (n : ℕ) :
    IsCompact {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
  have hcube : IsCompact
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (-Real.pi) Real.pi) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hcube.of_isClosed_subset (isClosed_sixVertexClosedRootSimplex n)
  intro p hp
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  exact fun j => (hp.2.2 j)

theorem sixVertexBetheUpdate_closed_to_open {c : ℝ} (hc : 2 < c)
    {N n : ℕ} (hhalf : 2 * n ≤ N) {p : Fin n → ℝ}
    (hp : SixVertexClosedRootSimplex p) :
    SixVertexOpenRootSimplex (sixVertexBetheUpdate c N n p) := by
  rcases hp with ⟨hmono, hsymm, hinterval⟩
  constructor
  · by_cases hn : n = 0
    · subst n
      exact fun i => Fin.elim0 i
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
      exact sixVertexBetheUpdate_strictMono_of_monotone hc hN hmono
  constructor
  · exact sixVertexBetheUpdate_symmetric c hsymm
  · intro j
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    have hN : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * n) hhalf
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hsumPi := sum_sixVertexTheta_pi_of_symmetric c hsymm
    have hsumNegPi := sum_sixVertexTheta_neg_pi_of_symmetric c hsymm
    have hsumUpper :
        (∑ k, sixVertexTheta c Real.pi (p k)) ≤
          ∑ k, sixVertexTheta c (p j) (p k) := by
      apply Finset.sum_le_sum
      intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k)).antitone (hinterval j).2
    have hsumLower :
        (∑ k, sixVertexTheta c (p j) (p k)) ≤
          ∑ k, sixVertexTheta c (-Real.pi) (p k) := by
      apply Finset.sum_le_sum
      intro k _
      exact (strictAnti_sixVertexTheta_left hc (p k)).antitone (hinterval j).1
    have hjlt : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : ℝ) + 1 ≤ (n : ℝ) := by
      have hjint : (j.val : ℤ) < n := by exact_mod_cast j.isLt
      exact_mod_cast hjint
    have hIupper : sixVertexCentralQuantumNumber j ≤ ((n : ℝ) - 1) / 2 := by
      rw [sixVertexCentralQuantumNumber_eq]
      linarith
    have hIlower : -((n : ℝ) - 1) / 2 ≤ sixVertexCentralQuantumNumber j := by
      rw [sixVertexCentralQuantumNumber_eq]
      have hjnonneg : (0 : ℝ) ≤ j.val := by positivity
      linarith
    have hhalfre : (2 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhalf
    have hcount : (2 : ℝ) * (n : ℝ) - 1 < (N : ℝ) := by
      have hnre : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    unfold sixVertexBetheUpdate
    constructor
    · apply (lt_div_iff₀ hNreal).mpr
      rw [hsumNegPi] at hsumLower
      nlinarith [Real.pi_pos]
    · apply (div_lt_iff₀ hNreal).mpr
      rw [hsumPi] at hsumUpper
      nlinarith [Real.pi_pos]

theorem SixVertexOpenRootSimplex.toClosed {n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexOpenRootSimplex p) : SixVertexClosedRootSimplex p := by
  rcases hp with ⟨hmono, hsymm, hinterval⟩
  exact ⟨hmono.monotone, hsymm, fun j =>
    ⟨(hinterval j).1.le, (hinterval j).2.le⟩⟩

theorem sixVertexBetheUpdate_mapsTo_closedRootSimplex {c : ℝ}
    (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    Set.MapsTo (sixVertexBetheUpdate c N n)
      {p | SixVertexClosedRootSimplex p}
      {p | SixVertexClosedRootSimplex p} := by
  intro p hp
  exact (sixVertexBetheUpdate_closed_to_open hc hhalf hp).toClosed

theorem sixVertexBetheUpdate_fixedPoint_mem_open {c : ℝ}
    (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N)
    {p : Fin n → ℝ} (hp : SixVertexClosedRootSimplex p)
    (hfix : sixVertexBetheUpdate c N n p = p) :
    SixVertexOpenRootSimplex p := by
  rw [← hfix]
  exact sixVertexBetheUpdate_closed_to_open hc hhalf hp

theorem sixVertexBetheUpdate_fixedPoint_is_solution {c : ℝ}
    {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ}
    (hfix : sixVertexBetheUpdate c N n p = p) :
    SixVertexSatisfiesBetheEquations c N n p :=
  (sixVertexBetheUpdate_eq_self_iff hN p).mp hfix

theorem sum_sixVertexTheta_pair (c : ℝ) {n : ℕ} (p : Fin n → ℝ) :
    ∑ j, ∑ k, sixVertexTheta c (p j) (p k) = 0 := by
  let S := ∑ j, ∑ k, sixVertexTheta c (p j) (p k)
  have hneg : S = -S := by
    calc
      S = ∑ j, ∑ k, -sixVertexTheta c (p k) (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        exact sixVertexTheta_antisymm c (p k) (p j)
      _ = -(∑ j, ∑ k, sixVertexTheta c (p k) (p j)) := by
        simp
      _ = -S := by
        rw [Finset.sum_comm]
  linarith


theorem SixVertexSatisfiesBetheEquations.sum_eq_zero
    {c : ℝ} {N n : ℕ} (hN : 0 < N) {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    ∑ j, p j = 0 := by
  have hsum :
      (∑ j, (N : ℝ) * p j) =
        ∑ j, (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ k, sixVertexTheta c (p j) (p k)) := by
    exact Finset.sum_congr rfl (fun j _ => hp j)
  have htheta := sum_sixVertexTheta_pair c p
  have hquantum := sum_sixVertexCentralQuantumNumber n
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [hquantum, mul_zero, htheta, sub_zero] at hsum
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith



theorem SixVertexSatisfiesBetheEquations.reverse_neg
    {c : ℝ} {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    SixVertexSatisfiesBetheEquations c N n (fun j => -p j.rev) := by
  intro j
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k.rev)) =
        ∑ k : Fin n, sixVertexTheta c (p j.rev) (p k) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hj := hp j.rev
  rw [sixVertexCentralQuantumNumber_rev] at hj
  simp only [sixVertexTheta_neg]
  rw [Finset.sum_neg_distrib, hsum]
  nlinarith

end

end StatMech.FrontierD
