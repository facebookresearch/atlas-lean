/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Ranges of traces and real parts of word maps (Kourovka Notebook Problem 16.69)

A nontrivial word in two variables omits the real part `0` on nonzero real quaternions,
refuting the real-part property in Kourovka Notebook Problem 16.69(b).
A finite cover of the norm-one sphere supplies a finite list of powers, one of which is
close to the identity at every input. Iterated commutators contract near that power,
and further commutators combine the resulting words into a single witness.

Kourovka Notebook, Problem 16.69 (J. Mycielski): let `W` be a non-trivial reduced group word in two
variables. a) Must the range of `Tr(W(x, y))` for `x, y ∈ GL(2, ℝ)` include the interval `[-2, +∞)`?
b) For `x, y` non-zero quaternions, must the range of `Re(W(x, y))` include the interval `[-5/27,
1]`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski). UnsolvedMath record
UM-00701261 (`KOU-16.69`), dataset ulamai/UnsolvedMath v1.8.0.

Words are nontrivial elements of `F₂` evaluated by `x₀ ↦ x`, `x₁ ↦ y`; non-zero quaternions are the
units of `Quaternion ℝ`, and `Re` is the real part `re`. Part (a) keeps `GL(2, ℝ)` as posed: the
Notebook's answer "No" is to this question, while the cited Theorem 2 is stated for `SL(2, ℝ)`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted

/-- **Mycielski's real-part property for quaternion word maps (Kourovka 16.69(b)).** For every
nontrivial element $w$ of the free group on two generators $x, y$, the set of real parts
$\operatorname{Re} w(p, q)$, where $p, q$ range over the nonzero real quaternions and $w(p, q)$ is
obtained by substituting $p$ for $x$ and $q$ for $y$, contains the interval $[-5/27, 1]$. -/
def quaternionRealPartRangeContainsInterval : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Icc (-5 / 27 : ℝ) 1 ⊆ Set.range fun xy : (Quaternion ℝ)ˣ × (Quaternion ℝ)ˣ =>
      (FreeGroup.lift ![xy.1, xy.2] w : Quaternion ℝ).re

namespace quaternionRealPartRangeContainsInterval_refuted

open scoped commutatorElement

local notation "ℍ" => Quaternion ℝ
local notation "F₂" => FreeGroup (Fin 2)
local notation "X" => (FreeGroup.of (0 : Fin 2))
local notation "Y" => (FreeGroup.of (1 : Fin 2))

private noncomputable def normUnits : ℍˣ →* ℝˣ :=
  Units.map (normHom : ℍ →*₀ ℝ).toMonoidHom

private def scalarUnits : ℝˣ →* ℍˣ :=
  Units.map (algebraMap ℝ ℍ).toMonoidHom

private theorem scalarUnits_commute (r : ℝˣ) (u : ℍˣ) : Commute (scalarUnits r) u := by
  apply Units.ext
  exact Quaternion.coe_commutes (r : ℝ) (u : ℍ)

private noncomputable def normalize : ℍˣ →* ℍˣ where
  toFun u := u * scalarUnits ((normUnits u)⁻¹)
  map_one' := by simp
  map_mul' u v := by
    change u * v * scalarUnits ((normUnits (u * v))⁻¹) = _
    rw [map_mul normUnits, mul_inv_rev, mul_comm (normUnits v)⁻¹, map_mul]
    exact (scalarUnits_commute _ _).mul_mul_mul_comm _ _ |>.symm

private theorem norm_normalize (u : ℍˣ) : ‖(normalize u : ℍ)‖ = 1 := by
  change ‖(u : ℍ) * ((↑((normUnits u)⁻¹) : ℝ) : ℍ)‖ = 1
  rw [Units.val_inv_eq_inv_val]
  change ‖(u : ℍ) * ((‖(u : ℍ)‖)⁻¹ : ℝ)‖ = 1
  rw [norm_mul, Quaternion.norm_coe, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Units.ne_zero u))]

private noncomputable abbrev Sphere := normUnits.ker

private noncomputable def quat : Sphere →* ℍ := Units.coeHom ℍ |>.comp normUnits.ker.subtype

private theorem norm_quat (u : Sphere) : ‖quat u‖ = 1 :=
  congrArg Units.val (show normUnits u.val = 1 from u.prop)

private theorem norm_sub_one_conj (u v : Sphere) :
    ‖quat (u * v * u⁻¹) - 1‖ = ‖quat v - 1‖ := by
  rw [show quat (u * v * u⁻¹) - 1 = quat u * (quat v - 1) * quat u⁻¹ by
    simp only [mul_sub, mul_one, sub_mul, ← map_mul]
    rw [mul_inv_cancel, map_one]]
  simp [norm_mul, norm_quat]

private theorem commutator_bound (u v : Sphere) :
    ‖quat ⁅u, v⁆ - 1‖ ≤ (2 * ‖quat u - 1‖) * ‖quat v - 1‖ := by
  let a := quat u - 1
  let b := quat v - 1
  have heq : quat ⁅u, v⁆ - 1 = (a * b - b * a) * quat (u⁻¹ * v⁻¹) := by
    have h : a * b - b * a = quat u * quat v - quat v * quat u := by
      dsimp [a, b]
      noncomm_ring
    rw [h, sub_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      ← mul_inv_rev, mul_inv_cancel, map_one, commutatorElement_def, mul_assoc (u * v), mul_inv_rev]
  rw [heq, norm_mul, norm_quat, mul_one]
  calc
    ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ = (2 * ‖a‖) * ‖b‖ := by rw [norm_mul, norm_mul, mul_comm ‖b‖, two_mul, add_mul]

private theorem norm_sub_one_le_two (u : Sphere) : ‖quat u - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖quat u‖ + ‖(1 : ℍ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_quat, norm_one, one_add_one_eq_two]

private theorem basic_commutators_do_not_commute : ¬ Commute ⁅X, Y⁆ ⁅X, Y ^ 2⁆ := by
  rw [← commutatorElement_eq_one_iff_commute]
  intro h
  have he := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_one] at he
  exact (by decide : FreeGroup.toWord ⁅⁅X, Y⁆, ⁅X, Y ^ 2⁆⁆ ≠ []) he

-- Conjugation can keep two nontrivial words from commuting.
private theorem exists_nontrivial_join {a b : F₂} (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ t : F₂, ⁅a, MulAut.conj t b⁆ ≠ 1 := by
  by_contra! h
  have hab : Commute a b := by
    simpa only [map_one, MulAut.one_apply] using commutatorElement_eq_one_iff_commute.mp (h 1)
  obtain ⟨d, hd⟩ := IsFreeGroup.isCyclic_centralizer ha
  let c : F₂ := d.val
  have hca : Commute c a := Subgroup.mem_centralizer_singleton_iff.mp d.prop
  have hc : c ≠ 1 := by
    obtain ⟨n, hn⟩ := hd ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    intro h1
    apply ha
    simpa only [Subgroup.coe_zpow, show d.val = 1 from h1, one_zpow] using
      (congrArg Subtype.val hn).symm
  have hcb := IsFreeGroup.commute_trans hca hab ha
  have hpow (g : F₂) : ∃ n : ℤ, MulAut.conj g c = c ^ n := by
    have hga := commutatorElement_eq_one_iff_commute.mp (h g)
    have hg1 : MulAut.conj g b ≠ 1 := by
      rw [← (MulAut.conj g).map_one]
      exact (MulAut.conj g).injective.ne hb
    have hgc := IsFreeGroup.commute_trans (hcb.map (MulAut.conj g)) hga.symm hg1
    obtain ⟨n, hn⟩ := hd ⟨MulAut.conj g c, Subgroup.mem_centralizer_singleton_iff.mpr hgc.eq⟩
    exact ⟨n, (congrArg Subtype.val hn).symm⟩
  -- Conjugations act by powers on the cyclic centralizer, so commute there.
  have hcomm (g k : F₂) : Commute ⁅g⁻¹, k⁻¹⁆ c := by
    obtain ⟨m, hm⟩ := hpow g
    obtain ⟨n, hn⟩ := hpow k
    have hcomp : MulAut.conj (g * k) c = MulAut.conj (k * g) c := by
      simp only [map_mul, MulAut.mul_apply, hn, hm, map_zpow, ← zpow_mul]
      rw [mul_comm m n]
    have hfix := congrArg ((MulAut.conj (k * g)).symm) hcomp
    rw [MulEquiv.symm_apply_apply] at hfix
    change ((MulAut.conj (k * g))⁻¹ * MulAut.conj (g * k)) c = c at hfix
    rw [← map_inv, ← map_mul, show (k * g)⁻¹ * (g * k) = ⁅g⁻¹, k⁻¹⁆ by
      simp only [mul_inv_rev, commutatorElement_def, inv_inv, mul_assoc]] at hfix
    exact (commute_iff_eq _ _).mpr (by
      simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using
        congrArg (· * ⁅g⁻¹, k⁻¹⁆) hfix)
  exact basic_commutators_do_not_commute (IsFreeGroup.commute_trans
    (by simpa only [inv_inv] using hcomm X⁻¹ Y⁻¹)
    (by simpa only [inv_inv] using (hcomm X⁻¹ (Y ^ 2)⁻¹).symm) hc)

private def engel {G : Type*} [Group G] (a b : G) : ℕ → G
  | 0 => b
  | n + 1 => ⁅a, engel a b n⁆

private theorem map_engel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (n : ℕ) :
    f (engel a b n) = engel (f a) (f b) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [engel, map_commutatorElement, ih]

private def exponent : F₂ →* Multiplicative ℤ :=
  FreeGroup.lift ![Multiplicative.ofAdd 1, 1]

private theorem exp_X : exponent X = Multiplicative.ofAdd 1 := by
  simp [exponent]

private theorem engel_ne_one {m : ℕ} (hm : 0 < m) (n : ℕ) : engel (X ^ m) Y n ≠ 1 := by
  have hXm : X ^ m ≠ 1 := by
    intro h
    have he := congrArg (fun w ↦ (exponent w).toAdd) h
    simp [exp_X] at he
    omega
  have hexp (k : ℕ) : exponent (engel (X ^ m) Y k) = 1 := by
    cases k with
    | zero => simp [engel, exponent]
    | succ k =>
      rw [engel, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
  induction n with
  | zero =>
    change Y ≠ 1
    simp [FreeGroup.of_ne_one]
  | succ n ih =>
    intro hn
    have hh : Commute (X ^ m) (engel (X ^ m) Y n) :=
      commutatorElement_eq_one_iff_commute.mp hn
    have hc := IsFreeGroup.commute_trans ((Commute.refl X).pow_right m) hh hXm
    obtain ⟨k, hk⟩ := FreeGroup.commute_of_iff.mp hc
    have hk0 : k = 0 := by
      simpa [exp_X, hexp] using congrArg (fun w ↦ (exponent w).toAdd) hk
    exact ih (by simpa only [hk0, zpow_zero] using hk.symm)

private theorem engel_bound {a : Sphere} (ha : ‖quat a - 1‖ < 1 / 4) (b : Sphere) (n : ℕ) :
    ‖quat (engel a b n) - 1‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simpa [engel] using norm_sub_one_le_two b
  | succ n ih =>
    rw [engel, pow_succ, ← mul_assoc]
    calc
      _ ≤ (2 * ‖quat a - 1‖) * ‖quat (engel a b n) - 1‖ := commutator_bound _ _
      _ ≤ _ := by
        rw [mul_comm _ (1 / 2 : ℝ)]
        exact mul_le_mul (by linarith) ih (norm_nonneg _) (by norm_num)

-- A finite cover of the sphere gives a close pair of powers by the pigeonhole principle.
private theorem exists_uniform_small_power :
    ∃ N : ℕ, ∀ u : Sphere, ∃ n ≤ N, 0 < n ∧ ‖quat (u ^ n) - 1‖ < 1 / 4 := by
  classical
  have : FiniteDimensional ℝ ℍ := FiniteDimensional.of_injective
    Quaternion.linearIsometryEquivTuple.toLinearMap Quaternion.linearIsometryEquivTuple.injective
  obtain ⟨centers, hfin, hcov⟩ :=
    Metric.totallyBounded_iff.mp (isCompact_sphere (0 : ℍ) 1).totallyBounded (1 / 8) (by norm_num)
  let _ : Fintype centers := hfin.fintype
  let N := Fintype.card centers
  refine ⟨N, fun u ↦ ?_⟩
  have hcenter (n : ℕ) : ∃ c : centers, dist (quat (u ^ n)) (c : ℍ) < 1 / 8 := by
    have hw : quat (u ^ n) ∈ Metric.sphere (0 : ℍ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_quat]
    simpa only [Set.mem_iUnion, Metric.mem_ball, SetCoe.exists] using hcov hw
  choose f hf using hcenter
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) ↦ f (k : ℕ)) (by simp [N])
  suffices hsmall : ∀ i j : Fin (N + 1), i < j → f i = f j →
      ∃ n ≤ N, 0 < n ∧ ‖quat (u ^ n) - 1‖ < 1 / 4 by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hsmall i j hij heq
    · exact hsmall j i hji heq.symm
  intro i j hij heq
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  refine ⟨(j : ℕ) - i, by omega, by omega, ?_⟩
  have hp : u ^ (j : ℕ) * (u ^ (i : ℕ))⁻¹ = u ^ ((j : ℕ) - i) := by
    calc
      _ = u ^ ((j : ℕ) - i) * u ^ (i : ℕ) * (u ^ (i : ℕ))⁻¹ := by
        rw [← pow_add, Nat.sub_add_cancel hij'.le]
      _ = _ := mul_inv_cancel_right _ _
  rw [← hp, map_mul]
  have hdist : dist (quat (u ^ (j : ℕ))) (quat (u ^ (i : ℕ))) < 1 / 4 := by
    have hi := hf i
    have hj := hf j
    rw [heq] at hi
    calc
      _ ≤ dist (quat (u ^ (j : ℕ))) (f j : ℍ) + dist (f j : ℍ) (quat (u ^ (i : ℕ))) :=
        dist_triangle _ _ _
      _ < _ := by rw [dist_comm (f j : ℍ)]; linarith
  calc
    ‖quat (u ^ (j : ℕ)) * quat (u ^ (i : ℕ))⁻¹ - 1‖ =
        ‖(quat (u ^ (j : ℕ)) - quat (u ^ (i : ℕ))) * quat (u ^ (i : ℕ))⁻¹‖ := by
      rw [sub_mul, ← map_mul quat (u ^ (i : ℕ)), mul_inv_cancel, map_one]
    _ = dist (quat (u ^ (j : ℕ))) (quat (u ^ (i : ℕ))) := by
      rw [norm_mul, norm_quat, mul_one, dist_eq_norm]
    _ < 1 / 4 := hdist

private def eval {G : Type*} [Group G] (x y : G) : F₂ →* G :=
  FreeGroup.lift ![x, y]

-- Join the words for the first N exponents with an Engel word for exponent N+1.
private theorem uniform_word (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : F₂, ⁅a, b⁆ ≠ 1 ∧ ∀ x y : Sphere,
      (∃ n ≤ N, 0 < n ∧ ‖quat (x ^ n) - 1‖ < 1 / 4) →
        ‖quat (eval x y ⁅a, b⁆) - 1‖ < ε := by
  induction N generalizing ε with
  | zero =>
    refine ⟨X, Y, ?_, ?_⟩
    · simpa [engel] using engel_ne_one (m := 1) (by decide) 1
    · rintro x y ⟨n, hn, hpos, -⟩
      omega
  | succ N ih =>
    obtain ⟨a, b, hab, hprev⟩ := ih (ε / 4) (by positivity)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    let a' := X ^ (N + 1)
    let b' := engel a' Y k
    have hab' : ⁅a', b'⁆ ≠ 1 := engel_ne_one (Nat.succ_pos N) (k + 1)
    obtain ⟨t, ht⟩ := exists_nontrivial_join hab hab'
    refine ⟨⁅a, b⁆, MulAut.conj t ⁅a', b'⁆, ht, fun x y ⟨n, hn, hpos, hsmall⟩ ↦ ?_⟩
    let u := eval x y ⁅a, b⁆
    let v := eval x y ⁅a', b'⁆
    let s := eval x y t
    have he : eval x y ⁅⁅a, b⁆, MulAut.conj t ⁅a', b'⁆⁆ = ⁅u, s * v * s⁻¹⁆ := by
      rw [map_commutatorElement]
      simp only [u, v, s, MulAut.conj_apply, map_mul, map_inv]
    rw [he]
    have hbound := commutator_bound u (s * v * s⁻¹)
    rw [norm_sub_one_conj] at hbound
    by_cases hle : n ≤ N
    · have hu : ‖quat u - 1‖ < ε / 4 := hprev x y ⟨n, hle, hpos, hsmall⟩
      calc
        _ ≤ _ := hbound
        _ ≤ (2 * ‖quat u - 1‖) * 2 :=
          mul_le_mul_of_nonneg_left (norm_sub_one_le_two v) (by positivity)
        _ < ε := by linarith
    · have hn' : n = N + 1 := by omega
      have hv : v = engel (x ^ (N + 1)) y (k + 1) := by
        change eval x y (engel (X ^ (N + 1)) Y (k + 1)) = _
        simp [map_engel, eval, map_pow]
      have hvsmall : ‖quat v - 1‖ < ε / 4 := by
        rw [hv]
        refine (engel_bound (hn' ▸ hsmall) y (k + 1)).trans_lt ?_
        rwa [pow_succ, ← mul_assoc, mul_comm 2, mul_assoc, show 2 * (1 / 2 : ℝ) = 1 by norm_num,
          mul_one]
      calc
        _ ≤ _ := hbound
        _ ≤ (2 * 2) * ‖quat v - 1‖ := by
          gcongr
          exact norm_sub_one_le_two u
        _ < ε := by linarith

private noncomputable def normalizeSphere : ℍˣ →* Sphere :=
  normalize.codRestrict Sphere fun u ↦ Units.ext (norm_normalize u)

private theorem normalize_eq_self_of_norm_one {u : ℍˣ} (hu : ‖(u : ℍ)‖ = 1) :
    normalize u = u := by
  have h : normUnits u = 1 := Units.ext hu
  simp [normalize, h]

private theorem quaternion_eval_bound :
    ∃ w : F₂, w ≠ 1 ∧ ∀ x y : ℍˣ, ‖(eval x y w : ℍ) - 1‖ < 1 := by
  obtain ⟨N, hN⟩ := exists_uniform_small_power
  obtain ⟨a, b, hab, hw⟩ := uniform_word N 1 zero_lt_one
  refine ⟨⁅a, b⁆, hab, fun x y ↦ ?_⟩
  have he (w : F₂) : normalizeSphere (eval x y w) =
      eval (normalizeSphere x) (normalizeSphere y) w :=
    FreeGroup.lift_unique (normalizeSphere.comp (eval x y)) (by
      intro i
      fin_cases i <;> simp [eval])
  have hn : ‖(eval x y ⁅a, b⁆ : ℍ)‖ = 1 := by
    change ↑(normUnits (eval x y ⁅a, b⁆)) = (1 : ℝ)
    rw [← MonoidHom.comp_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)]
    rfl
  have h := hw (normalizeSphere x) (normalizeSphere y) (hN _)
  rw [← he] at h
  change ‖(normalize (eval x y ⁅a, b⁆) : ℍ) - 1‖ < 1 at h
  simpa only [normalize_eq_self_of_norm_one hn] using h

end quaternionRealPartRangeContainsInterval_refuted

/-- **Mycielski's real-part question for quaternion word maps has a negative answer.** There is a
nontrivial element $w$ of the free group on two generators $x, y$ such that some real number $t$
with $-5/27 \le t \le 1$ is not the real part of $w(p, q)$ for any nonzero real quaternions $p, q$,
where $w(p, q)$ is obtained by substituting $p$ for $x$ and $q$ for $y$.

Resolved false: the Kourovka Notebook (21st issue) answers 16.69(b) "No, it need not", citing Thom
(2013), whose Corollary 1.2 gives, for every `n` and `ε > 0`, a word `w ≠ 1` with `‖1 - w(u, v)‖ ≤
ε` for all `u, v ∈ U(n)`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski);
resolution: Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September
2026); A. Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, (a)
Nilradical, Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ)); (b) Thom,
Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)); the
Kourovka Notebook (21st issue) marks 16.69 solved (a: No, AI solution confirmed by A. Thom; b: No,
Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
theorem quaternionRealPartRangeContainsInterval_refuted :
    ¬ quaternionRealPartRangeContainsInterval := by
  intro h
  obtain ⟨w, hw, hbound⟩ := quaternionRealPartRangeContainsInterval_refuted.quaternion_eval_bound
  have hz : (0 : ℝ) ∈ Set.Icc (-5 / 27 : ℝ) 1 := by norm_num
  obtain ⟨⟨x, y⟩, hxy⟩ := h w hw hz
  let q : Quaternion ℝ := ↑(quaternionRealPartRangeContainsInterval_refuted.eval x y w)
  change q.re = 0 at hxy
  have hdist : ‖q - 1‖ < 1 := hbound x y
  have hs := Quaternion.normSq_def' (q - 1)
  rw [Quaternion.normSq_eq_norm_mul_self, Quaternion.re_sub, Quaternion.re_one, hxy] at hs
  nlinarith only [hs, hdist, norm_nonneg (q - 1), sq_nonneg (q - 1).imI,
    sq_nonneg (q - 1).imJ, sq_nonneg (q - 1).imK]

end MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted
