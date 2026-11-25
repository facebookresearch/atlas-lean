/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Path-sum expansion and denominator-scaled integrality

For a circuit `g₁, …, gₖ` of 2-local gates, the amplitude
`⟨s| Uₖ ⋯ U₁ |t⟩` is a sum over intermediate basis sequences ("paths") of
products of gate entries. This file states the expansion recursively
(`ampSum`), proves it computes `applyCircuit` on well-formed gates, and
clears denominators: gate entries are Gaussian rationals read off the
encoded entry lists, so scaling an amplitude by the product of the gate
denominators gives a Gaussian integer, and the acceptance probability of a
basis initial state times that squared scale is a natural number. This is the
counting form behind the usual path-integral view of quantum circuits.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4; A. Y. Kitaev,
A. H. Shen, and M. N. Vyalyi, Classical and Quantum Computation, American
Mathematical Society, 2002.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

/-- **Path-sum amplitude.** `ampSum N gs s t` is the sum over all
intermediate basis sequences of the product of gate-matrix entries along
the sequence, from input basis index `t` to output basis index `s`,
organized by recursion on the gate list: the head gate is applied first. -/
noncomputable def ampSum (N : ℕ) : List QGate → Fin (2 ^ N) → Fin (2 ^ N) → ℂ
  | [], s, t => if s = t then 1 else 0
  | g :: gs, s, t => ∑ u, ampSum N gs s u * gateMatrix N g u t

/-- **Path-sum expansion:** applying a well-formed circuit is summing
path amplitudes against the initial state. -/
theorem applyCircuit_eq_ampSum {N : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g) (ψ : Fin (2 ^ N) → ℂ)
    (s : Fin (2 ^ N)) :
    applyCircuit N gs ψ s = ∑ t, ampSum N gs s t * ψ t := by
  induction gs generalizing ψ with
  | nil =>
    simp only [applyCircuit, List.foldl_nil, ampSum]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  | cons g gs ih =>
    have hg : QGateWellFormed N g := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g' ∈ gs, QGateWellFormed N g' :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hfold : applyCircuit N (g :: gs) ψ = applyCircuit N gs (applyGate N g ψ) := by
      simp [applyCircuit]
    rw [hfold, ih hgs', applyGate_eq_gateMatrix_mulVec hg]
    simp only [Matrix.mulVec_apply_eq_sum, ampSum]
    calc ∑ t, ampSum N gs s t * (∑ u, gateMatrix N g t u * ψ u)
        = ∑ t, ∑ u, ampSum N gs s t * (gateMatrix N g t u * ψ u) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
      _ = ∑ u, ∑ t, ampSum N gs s t * (gateMatrix N g t u * ψ u) := Finset.sum_comm
      _ = ∑ u, (∑ t, ampSum N gs s t * gateMatrix N g t u) * ψ u := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          ring

/-- **Denominator of an encoded rational,** taken as `1` when the stored
denominator is `0` (in which case the encoded value is `0`). -/
def ratDenom (e : RatEnc) : ℕ := max e.2.2 1

private theorem ratDenom_pos (e : RatEnc) : 0 < ratDenom e := by
  unfold ratDenom
  omega

/-- Every encoded rational is an integer over its `ratDenom`. -/
theorem toRat_eq_div (e : RatEnc) :
    ∃ a : ℤ, toRat e = (a : ℚ) / (ratDenom e : ℚ) := by
  rcases e with ⟨sign, num, den⟩
  simp only [toRat, ratDenom]
  by_cases hd : den = 0
  · refine ⟨0, ?_⟩
    simp [hd]
  · have hmax : max den 1 = den := by omega
    rw [hmax]
    cases sign
    · refine ⟨(num : ℤ), ?_⟩
      simp
    · refine ⟨-(num : ℤ), ?_⟩
      simp

/-- **Common denominator of a gate's entries:** the product of the encoded
denominators appearing in its entry list. -/
def gateDenom (g : QGate) : ℕ :=
  (g.2.2.map (fun p => ratDenom p.1 * ratDenom p.2)).prod

/-- The gate denominator is positive. -/
theorem gateDenom_pos (g : QGate) : 0 < gateDenom g := by
  unfold gateDenom
  apply List.prod_pos
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨p, hp, rfl⟩
  have h1 := ratDenom_pos p.1
  have h2 := ratDenom_pos p.2
  positivity

private theorem toComplex_mem_gaussian (g : QGate) (p : RatEnc × RatEnc) (hp : p ∈ g.2.2) :
    ∃ a b : ℤ, toComplex p =
      ⟨(a : ℝ) / (gateDenom g : ℝ), (b : ℝ) / (gateDenom g : ℝ)⟩ := by
  obtain ⟨a1, ha1⟩ := toRat_eq_div p.1
  obtain ⟨a2, ha2⟩ := toRat_eq_div p.2
  have hmem : ratDenom p.1 * ratDenom p.2 ∈ g.2.2.map (fun p => ratDenom p.1 * ratDenom p.2) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have hdvd : ratDenom p.1 * ratDenom p.2 ∣ gateDenom g := by
    unfold gateDenom
    exact List.dvd_prod hmem
  obtain ⟨k, hk⟩ := hdvd
  have h1 := ratDenom_pos p.1
  have h2 := ratDenom_pos p.2
  have hD := gateDenom_pos g
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro hk0
      rw [hk0, mul_zero] at hk
      omega
    exact Nat.pos_of_ne_zero hne
  refine ⟨a1 * (ratDenom p.2 : ℤ) * (k : ℤ), a2 * (ratDenom p.1 : ℤ) * (k : ℤ), ?_⟩
  unfold toComplex
  apply Complex.ext
  · simp only
    rw [ha1]
    have h1R : (0 : ℝ) < (ratDenom p.1 : ℝ) := by exact_mod_cast h1
    have h2R : (0 : ℝ) < (ratDenom p.2 : ℝ) := by exact_mod_cast h2
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    rw [hk]
    push_cast
    field_simp
  · simp only
    rw [ha2]
    have h1R : (0 : ℝ) < (ratDenom p.1 : ℝ) := by exact_mod_cast h1
    have h2R : (0 : ℝ) < (ratDenom p.2 : ℝ) := by exact_mod_cast h2
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    rw [hk]
    push_cast
    field_simp

/-- **Gate entries are Gaussian rationals over `gateDenom`:** every entry of
`gateMatrix N g` is a Gaussian integer divided by `gateDenom g`. -/
theorem gateMatrix_entry_gaussian (N : ℕ) (g : QGate)
    (s t : Fin (2 ^ N)) :
    ∃ z : GaussianInt, gateMatrix N g s t = (z : ℂ) / ((gateDenom g : ℕ) : ℂ) := by
  unfold gateMatrix
  split_ifs with h
  · unfold matrixOfEntries
    set idx := qIdx2 (qBit g.1 s.val, qBit g.2.1 s.val) * 4 +
      qIdx2 (qBit g.1 t.val, qBit g.2.1 t.val) with hidx
    by_cases hlen : idx < g.2.2.length
    · rw [List.getD_eq_getElem g.2.2 _ hlen]
      obtain ⟨a, b, hab⟩ := toComplex_mem_gaussian g _ (List.getElem_mem hlen)
      refine ⟨⟨a, b⟩, ?_⟩
      rw [hab, GaussianInt.toComplex_def₂]
      apply Complex.ext
      · simp
      · simp
    · rw [List.getD_eq_default g.2.2 _ (Nat.le_of_not_gt hlen)]
      refine ⟨⟨0, 0⟩, ?_⟩
      have hdef : toComplex ((false, 0, 1), (false, 0, 1)) = 0 := by
        unfold toComplex toRat
        simp
        rfl
      rw [hdef, GaussianInt.toComplex_def₂]
      apply Complex.ext
      · simp
      · simp
  · refine ⟨⟨0, 0⟩, ?_⟩
    rw [GaussianInt.toComplex_def₂]
    apply Complex.ext
    · simp
    · simp

private theorem gateMatrix_mul_denom_gaussian (N : ℕ) (g : QGate)
    (s t : Fin (2 ^ N)) :
    ∃ a b : ℤ, gateMatrix N g s t * ((gateDenom g : ℕ) : ℂ) = ⟨(a : ℝ), (b : ℝ)⟩ := by
  obtain ⟨z, hz⟩ := gateMatrix_entry_gaussian N g s t
  refine ⟨z.re, z.im, ?_⟩
  rw [hz]
  have hD : ((gateDenom g : ℕ) : ℂ) ≠ 0 := by
    have hpos := gateDenom_pos g
    exact_mod_cast ne_of_gt hpos
  rw [div_mul_cancel₀ _ hD]
  exact GaussianInt.toComplex_def₂ z
/-- **Amplitudes clear denominators:** a path-sum amplitude times the
product of the gate denominators is a Gaussian integer. -/
theorem ampSum_mul_prod_gaussian (N : ℕ) (gs : List QGate)
    (s t : Fin (2 ^ N)) :
    ∃ z : GaussianInt, ampSum N gs s t *
        ((gs.map gateDenom).prod : ℂ) = (z : ℂ) := by
  induction gs generalizing s t with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Nat.cast_one, mul_one]
    simp only [ampSum]
    by_cases h : s = t
    · simp [h]
      refine ⟨⟨1, 0⟩, ?_⟩
      simp [GaussianInt.toComplex_def₂]
      rfl
    · simp [h]
      refine ⟨⟨0, 0⟩, ?_⟩
      simp [GaussianInt.toComplex_def₂]
      rfl
  | cons g gs ih =>
    have hprod : ((g :: gs).map gateDenom).prod = gateDenom g * (gs.map gateDenom).prod := by
      simp
    simp only [ampSum]
    have hIH : ∀ u, ∃ z : GaussianInt, ampSum N gs s u * (((gs.map gateDenom).prod : ℕ) : ℂ) = (z : ℂ) :=
      fun u => ih s u
    choose Z1 hZ1 using hIH
    have hG : ∀ u, ∃ a b : ℤ, gateMatrix N g u t * (((gateDenom g : ℕ)) : ℂ) = ⟨(a : ℝ), (b : ℝ)⟩ :=
      fun u => gateMatrix_mul_denom_gaussian N g u t
    choose A2 B2 hA2 using hG
    refine ⟨∑ u, (Z1 u * ⟨A2 u, B2 u⟩), ?_⟩
    rw [hprod, Nat.cast_mul, Finset.sum_mul]
    have hterm : ∀ u, (ampSum N gs s u * gateMatrix N g u t) * (((gateDenom g : ℕ) : ℂ) * (((gs.map gateDenom).prod : ℕ) : ℂ)) =
        (((Z1 u * ⟨A2 u, B2 u⟩ : GaussianInt)) : ℂ) := by
      intro u
      have hring : (ampSum N gs s u * gateMatrix N g u t) * (((gateDenom g : ℕ) : ℂ) * (((gs.map gateDenom).prod : ℕ) : ℂ)) =
          (ampSum N gs s u * (((gs.map gateDenom).prod : ℕ) : ℂ)) * (gateMatrix N g u t * (((gateDenom g : ℕ)) : ℂ)) := by
        ring
      rw [hring, hZ1 u]
      have hA2' : gateMatrix N g u t * (((gateDenom g : ℕ)) : ℂ) = (((⟨A2 u, B2 u⟩ : GaussianInt)) : ℂ) := by
        rw [hA2 u, GaussianInt.toComplex_def₂]
      rw [hA2', GaussianInt.toComplex_mul]
    have hsum : (∑ u, (ampSum N gs s u * gateMatrix N g u t) * (((gateDenom g : ℕ) : ℂ) * (((gs.map gateDenom).prod : ℕ) : ℂ))) =
        ∑ u, ((((Z1 u * ⟨A2 u, B2 u⟩ : GaussianInt))) : ℂ) :=
      Finset.sum_congr rfl (fun u _ => hterm u)
    rw [hsum, map_sum]

private theorem qNumOf_lt_aux (x : List Bool) : qNumOf x < 2 ^ x.length := by
  induction x with
  | nil => simp [qNumOf]
  | cons b bs ih =>
    simp only [qNumOf, List.length_cons, Nat.pow_succ]
    cases b
    · simp
      omega
    · simp
      omega

private theorem bqpInitState_eq_ite_aux (x : List Bool) (a : ℕ) (s : Fin (2 ^ (x.length + a))) :
    bqpInitState x a s = (if s.val = qNumOf x then 1 else 0) := by
  have hq := qNumOf_lt_aux x
  have hmod_q : qNumOf x % 2 ^ x.length = qNumOf x := Nat.mod_eq_of_lt hq
  have hdiv_q : qNumOf x / 2 ^ x.length = 0 := Nat.div_eq_of_lt hq
  unfold bqpInitState tensorProd basisState zeroState
  simp only
  by_cases h : s.val = qNumOf x
  · simp [h, hmod_q, hdiv_q]
  · simp only [h, ↓reduceIte]
    by_cases hmod : s.val % 2 ^ x.length = qNumOf x
    · by_cases hdiv : s.val / 2 ^ x.length = 0
      · exfalso
        have hdecomp := Nat.div_add_mod s.val (2 ^ x.length)
        rw [hdiv, hmod] at hdecomp
        simp at hdecomp
        exact h hdecomp.symm
      · simp [hmod, hdiv]
    · simp [hmod]

/-- **Denominator-scaled integrality of acceptance:** for a well-formed circuit
run on a basis initial state, the acceptance probability scaled by the
squared denominator product is a natural number. -/
theorem acceptProb_scaled_nat {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    ∃ n : ℕ, ((gs.map gateDenom).prod : ℝ) ^ 2 *
      acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) =
        (n : ℝ) := by
  have hq_lt_N : qNumOf x < 2 ^ (x.length + a) := by
    have h1 := qNumOf_lt_aux x
    have hle : 2 ^ x.length ≤ 2 ^ (x.length + a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set t0 : Fin (2 ^ (x.length + a)) := ⟨qNumOf x, hq_lt_N⟩ with ht0
  have ht0val : t0.val = qNumOf x := rfl
  have hamp : ∀ s, applyCircuit (x.length + a) gs (bqpInitState x a) s = ampSum (x.length + a) gs s t0 := by
    intro s
    rw [applyCircuit_eq_ampSum hgs]
    have hpsi : ∀ t, bqpInitState x a t = (if t = t0 then 1 else 0) := by
      intro t
      rw [bqpInitState_eq_ite_aux]
      by_cases h : t = t0
      · simp [h, ht0val]
      · have hval : t.val ≠ qNumOf x := by
          intro hcon
          apply h
          apply Fin.ext
          simp [ht0val, hcon]
        simp [h, hval]
    simp only [hpsi, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hacc : acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) =
      Finset.sum (Finset.univ.filter (fun s : Fin (2 ^ (x.length + a)) => qBit 0 s.val = 1))
        (fun s => Complex.normSq (ampSum (x.length + a) gs s t0)) := by
    unfold acceptProb
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : qBit 0 s.val = 1
    · simp only [h, ite_true]
      rw [hamp s]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    · simp [h]
  have hG : ∀ s, ∃ z : GaussianInt, ampSum (x.length + a) gs s t0 * (((gs.map gateDenom).prod : ℕ) : ℂ) = (z : ℂ) :=
    fun s => ampSum_mul_prod_gaussian (x.length + a) gs s t0
  choose Z hZ using hG
  have hnorm : ∀ s, (((gs.map gateDenom).prod : ℝ)) ^ 2 * Complex.normSq (ampSum (x.length + a) gs s t0) =
      ((Z s).norm : ℝ) := by
    intro s
    have hmul := congrArg Complex.normSq (hZ s)
    simp only [Complex.normSq_mul, Complex.normSq_natCast, ← GaussianInt.intCast_real_norm] at hmul
    calc (((gs.map gateDenom).prod : ℝ)) ^ 2 * Complex.normSq (ampSum (x.length + a) gs s t0)
        = Complex.normSq (ampSum (x.length + a) gs s t0) * ((((gs.map gateDenom).prod : ℝ)) * (((gs.map gateDenom).prod : ℝ))) := by ring
      _ = ((Z s).norm : ℝ) := hmul
  rw [hacc, Finset.mul_sum]
  refine ⟨Finset.sum (Finset.univ.filter (fun s : Fin (2 ^ (x.length + a)) => qBit 0 s.val = 1)) (fun s => (Z s).norm.natAbs), ?_⟩
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [hnorm s]
  have hnonneg : 0 ≤ (Z s).norm := GaussianInt.norm_nonneg _
  have htoNat : ((((Z s).norm.natAbs : ℕ) : ℤ)) = (Z s).norm := Int.natAbs_of_nonneg hnonneg
  calc ((Z s).norm : ℝ) = ((((Z s).norm.natAbs : ℕ) : ℤ) : ℝ) := by rw [htoNat]
    _ = ((((Z s).norm.natAbs : ℕ)) : ℝ) := by simp

end Cslib.Complexity.Classes
