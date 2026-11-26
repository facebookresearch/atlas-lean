/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PathSum
public import CSLibExt.Computability.Complexity.QuantumGates.BQPAudit
import Mathlib.Tactic

/-!
# Cleared-denominator path-pair gap and the sign lemma

Clearing the Gaussian-rational denominators of a circuit's path-sum
expansion gives Gaussian-integer path weights. For a circuit of well-formed
gates (unitary 2-local gates, `QGateWellFormed`) run on the BQP initial state
`bqpInitState x a`, the accept-minus-reject sum over pairs of paths with a
common end (`pathPairGap`, for paths from the initial index
`bqpInitIndex x a`) equals the squared product of the gate denominators times
`2 * acceptProb - 1`, so its sign is the sign of the acceptance probability
minus `1 / 2`. Unitarity is needed: it makes the total cleared weight equal to
that squared product. This is the counting form of the path-sum sign argument
behind `BQP ⊆ PP`; this module proves no complexity-class inclusion.

Source: S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 4,
Sec. 2.4 (path sums) and Sec. 2.6 (`BQP ⊆ PP`, the sign argument, an informal sketch);
R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Ch. 13.3.
Atlas gates have complex entries, so path pairs are weighted by the real
part of `pathNum p * star (pathNum q)`.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false


/-- **Signed numerator of an encoded rational.** The numerator field with the stored sign, or `0`
when the stored denominator is `0` (the encoded value is then `0` while the numerator field may be
nonzero). Together with `ratDenom`, `toRat e = ratNum e / ratDenom e`. -/
def ratNum (e : RatEnc) : ℤ :=
  if e.2.2 = 0 then 0 else if e.1 then -(e.2.1 : ℤ) else (e.2.1 : ℤ)

/-- **Cofactor of an entry.** The product of the denominator factors
`ratDenom p.1 * ratDenom p.2` of the entries of `es` other than the one at index `k`. -/
def entryCofactor (es : List (RatEnc × RatEnc)) (k : ℕ) : ℕ :=
  ((es.eraseIdx k).map (fun p => ratDenom p.1 * ratDenom p.2)).prod

/-- **Scaled entry.** The Gaussian-integer numerator of entry `k` of `es` over the product of all
entry denominators, and `0` past the end of the list. Uses only multiplication, so it needs no
division. -/
def entryNumAt (es : List (RatEnc × RatEnc)) (k : ℕ) : GaussianInt :=
  match es[k]? with
  | some p => ⟨ratNum p.1 * ((ratDenom p.2 * entryCofactor es k : ℕ) : ℤ),
      ratNum p.2 * ((ratDenom p.1 * entryCofactor es k : ℕ) : ℤ)⟩
  | none => 0

/-- **Scaled gate entry.** Entry `(s, t)` of `gateMatrix N g` times `gateDenom g`, as a Gaussian
integer, computed from the encoded entry list. -/
def gateEntryNum (N : ℕ) (g : QGate) (s t : Fin (2 ^ N)) : GaussianInt :=
  if (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
      qBit k.val s.val = qBit k.val t.val) then
    entryNumAt g.2.2 (qIdx2 (qBit g.1 s.val, qBit g.2.1 s.val) * 4 +
      qIdx2 (qBit g.1 t.val, qBit g.2.1 t.val))
  else 0

/-- **Cleared-denominator amplitude.** The recursion of `ampSum` with every gate entry replaced by
its scaled numerator `gateEntryNum`. -/
def ampNum (N : ℕ) : List QGate → Fin (2 ^ N) → Fin (2 ^ N) → GaussianInt
  | [], s, t => if s = t then 1 else 0
  | g :: gs, s, t => ∑ u, ampNum N gs s u * gateEntryNum N g u t

/-- **End of a computational path.** A path through `gs` from input index `t` lists the basis
state after each gate, head gate first; its end is the last of these, or `t` for no gates. -/
def pathEnd (N : ℕ) :
    (gs : List QGate) → (Fin gs.length → Fin (2 ^ N)) → Fin (2 ^ N) → Fin (2 ^ N)
  | [], _, t => t
  | _ :: gs, p, _ => pathEnd N gs (Fin.tail p) (p 0)

/-- **Weight of a computational path.** The product of the scaled gate entries along it. -/
def pathNum (N : ℕ) :
    (gs : List QGate) → (Fin gs.length → Fin (2 ^ N)) → Fin (2 ^ N) → GaussianInt
  | [], _, _ => 1
  | g :: gs, p, t => pathNum N gs (Fin.tail p) (p 0) * gateEntryNum N g (p 0) t

/-- **Output sign.** `1` on accepting basis states (qubit `0` is `1`), `-1` on the others. -/
def outSign {N : ℕ} (s : Fin (2 ^ N)) : ℤ := if qBit 0 s.val = 1 then 1 else -1

/-- **Accept-minus-reject path-pair gap.** The sum, over pairs of paths from the input index `t`
with a common end, of the output sign of that end times the real part of
`pathNum p * star (pathNum q)`. -/
def pathPairGap (N : ℕ) (gs : List QGate) (t : Fin (2 ^ N)) : ℤ :=
  ∑ p : Fin gs.length → Fin (2 ^ N), ∑ q : Fin gs.length → Fin (2 ^ N),
    if pathEnd N gs p t = pathEnd N gs q t then
      outSign (pathEnd N gs p t) * (pathNum N gs p t * star (pathNum N gs q t)).re
    else 0

/-- **Accepting cleared weight.** The sum of the norms `re ^ 2 + im ^ 2` of the cleared amplitudes
`ampNum N gs s t` over the accepting basis states `s` (qubit `0` is `1`). -/
def accWeight (N : ℕ) (gs : List QGate) (t : Fin (2 ^ N)) : ℤ :=
  ∑ s : Fin (2 ^ N), if qBit 0 s.val = 1 then (ampNum N gs s t).norm else 0

/-- **Basis index in a padded register.** The basis index `qNumOf x` of a bitstring `x` is less
than `2 ^ (x.length + a)` for every number `a` of ancilla qubits. -/
theorem qNumOf_lt_two_pow_add (x : List Bool) (a : ℕ) :
    qNumOf x < 2 ^ (x.length + a) := by
  have h : qNumOf x < 2 ^ x.length := by
    induction x with
    | nil => simp [qNumOf]
    | cons b bs ih =>
      simp only [qNumOf, List.length_cons, Nat.pow_succ]
      cases b <;> simp <;> omega
  calc qNumOf x < 2 ^ x.length := h
    _ ≤ 2 ^ (x.length + a) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Basis index of the BQP initial state.** The index `qNumOf x` in a register of
`x.length + a` qubits; `bqpInitState x a` is the basis vector at this index. -/
def bqpInitIndex (x : List Bool) (a : ℕ) : Fin (2 ^ (x.length + a)) :=
  ⟨qNumOf x, qNumOf_lt_two_pow_add x a⟩

private theorem toRat_eq_ratNum_div (e : RatEnc) :
    toRat e = (ratNum e : ℚ) / (ratDenom e : ℚ) := by
  obtain ⟨sgn, num, den⟩ := e
  simp only [toRat, ratNum, ratDenom]
  by_cases hden : den = 0
  · subst hden
    cases sgn <;> simp
  · have hpos : 1 ≤ den := Nat.pos_of_ne_zero hden
    have hmax : max den 1 = den := Nat.max_eq_left hpos
    rw [hmax]
    cases sgn <;> simp [hden]

private theorem gateDenom_eq_mul_entryCofactor (g : QGate) {k : ℕ} (hk : k < g.2.2.length) :
    gateDenom g = ratDenom g.2.2[k].1 * ratDenom g.2.2[k].2 * entryCofactor g.2.2 k := by
  unfold gateDenom entryCofactor
  have hlen : k < (g.2.2.map (fun p => ratDenom p.1 * ratDenom p.2)).length := by
    rw [List.length_map]
    exact hk
  have h := List.mul_prod_eraseIdx hlen (fun a' _ => Nat.mul_comm _ _)
  rw [List.eraseIdx_map] at h
  have hget : (g.2.2.map (fun p => ratDenom p.1 * ratDenom p.2))[k]'hlen =
      ratDenom g.2.2[k].1 * ratDenom g.2.2[k].2 :=
    List.getElem_map (fun p : RatEnc × RatEnc => ratDenom p.1 * ratDenom p.2)
      (h := hlen)
  rw [← h, hget]

private theorem toComplex_mul_scaled_entry (p : RatEnc × RatEnc) (cf D : ℕ)
    (hD : D = ratDenom p.1 * ratDenom p.2 * cf) :
    toComplex p * ((D : ℕ) : ℂ) = (↑(⟨ratNum p.1 * ((ratDenom p.2 * cf : ℕ) : ℤ),
      ratNum p.2 * ((ratDenom p.1 * cf : ℕ) : ℤ)⟩ : GaussianInt) : ℂ) := by
  have h1 := toRat_eq_ratNum_div p.1
  have h2 := toRat_eq_ratNum_div p.2
  have hd1 : (1:ℕ) ≤ ratDenom p.1 := by
    unfold ratDenom
    exact Nat.le_max_right _ _
  have hd2 : (1:ℕ) ≤ ratDenom p.2 := by
    unfold ratDenom
    exact Nat.le_max_right _ _
  have hd1R : ((ratDenom p.1 : ℕ) : ℝ) ≠ 0 := by
    have hne : ratDenom p.1 ≠ 0 := by omega
    exact_mod_cast hne
  have hd2R : ((ratDenom p.2 : ℕ) : ℝ) ≠ 0 := by
    have hne : ratDenom p.2 ≠ 0 := by omega
    exact_mod_cast hne
  have htre : (toComplex p).re = ((toRat p.1 : ℚ) : ℝ) := by simp [toComplex]
  have htim : (toComplex p).im = ((toRat p.2 : ℚ) : ℝ) := by simp [toComplex]
  have hre : ((↑(⟨ratNum p.1 * ((ratDenom p.2 * cf : ℕ) : ℤ),
      ratNum p.2 * ((ratDenom p.1 * cf : ℕ) : ℤ)⟩ : GaussianInt) : ℂ)).re =
      ((ratNum p.1 * ((ratDenom p.2 * cf : ℕ) : ℤ) : ℤ) : ℝ) :=
    GaussianInt.re_toComplex _ _
  have him : ((↑(⟨ratNum p.1 * ((ratDenom p.2 * cf : ℕ) : ℤ),
      ratNum p.2 * ((ratDenom p.1 * cf : ℕ) : ℤ)⟩ : GaussianInt) : ℂ)).im =
      ((ratNum p.2 * ((ratDenom p.1 * cf : ℕ) : ℤ) : ℤ) : ℝ) :=
    GaussianInt.im_toComplex _ _
  apply Complex.ext
  · rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero,
      htre, hre, h1, hD]
    push_cast
    field_simp [hd1R, hd2R]
  · rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_add,
      htim, him, h2, hD]
    push_cast
    field_simp [hd1R, hd2R]

/-- **Gate entries times the gate denominator.** For every gate `g`, entry `(s, t)` of
`gateMatrix N g` times `gateDenom g` is the Gaussian integer `gateEntryNum N g s t`. -/
theorem gateMatrix_mul_gateDenom (N : ℕ) (g : QGate) (s t : Fin (2 ^ N)) :
    gateMatrix N g s t * ((gateDenom g : ℕ) : ℂ) = (gateEntryNum N g s t : ℂ) := by
  simp only [gateMatrix, gateEntryNum]
  by_cases h : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
    qBit k.val s.val = qBit k.val t.val)
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [matrixOfEntries]
    set idx := qIdx2 (qBit g.1 s.val, qBit g.2.1 s.val) * 4 +
      qIdx2 (qBit g.1 t.val, qBit g.2.1 t.val)
    by_cases hlen : idx < g.2.2.length
    · have hsome : g.2.2[idx]? = some g.2.2[idx] := List.getElem?_eq_getElem hlen
      have hgetD := List.getD_eq_getElem (g.2.2) ((false, 0, 1), (false, 0, 1)) hlen
      have hG := gateDenom_eq_mul_entryCofactor g hlen
      simp only [hgetD, entryNumAt, hsome]
      exact toComplex_mul_scaled_entry _ _ _ hG
    · have hle : g.2.2.length ≤ idx := le_of_not_gt hlen
      have hnone : g.2.2[idx]? = none := List.getElem?_eq_none hle
      have hgetD := List.getD_eq_default (g.2.2) ((false, 0, 1), (false, 0, 1)) hle
      simp only [hgetD, entryNumAt, hnone]
      have hdef : toComplex ((false, 0, 1), (false, 0, 1)) = 0 := by
        apply Complex.ext <;> simp [toComplex, toRat]
      rw [hdef, zero_mul]
      exact (map_zero GaussianInt.toComplex).symm
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]
    exact (map_zero GaussianInt.toComplex).symm

/-- **Cleared and path-sum amplitudes.** For every circuit `gs`, the cleared amplitude
`ampNum N gs s t` is the path-sum amplitude `ampSum N gs s t` times the product of the gate
denominators. -/
theorem ampNum_eq_ampSum_mul (N : ℕ) (gs : List QGate) (s t : Fin (2 ^ N)) :
    (ampNum N gs s t : ℂ) = ampSum N gs s t * ((gs.map gateDenom).prod : ℂ) := by
  induction gs generalizing s t with
  | nil =>
    simp only [ampNum, ampSum, List.map_nil, List.prod_nil]
    by_cases h : s = t <;> simp [h]
  | cons g gs ih =>
    simp only [ampNum, ampSum, List.map_cons, List.prod_cons, Nat.cast_mul]
    show GaussianInt.toComplex _ = _
    rw [map_sum]
    simp only [map_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih]
    have h := gateMatrix_mul_gateDenom N g u t
    rw [← h]
    ring

private theorem sum_fun_fin_succ {α M : Type*} [Fintype α] [AddCommMonoid M] {k : ℕ}
    (F : (Fin (k + 1) → α) → M) :
    ∑ p : Fin (k + 1) → α, F p = ∑ a : α, ∑ r : Fin k → α, F (Fin.cons a r) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => α) F, Fintype.sum_prod_type]
  rfl

/-- **Integer path expansion.** The cleared amplitude `ampNum N gs s t` is the sum of the weights
`pathNum` of the paths from the input index `t` that end at the output index `s`. -/
theorem ampNum_eq_sum_pathNum (N : ℕ) (gs : List QGate) (s t : Fin (2 ^ N)) :
    ampNum N gs s t = ∑ p : Fin gs.length → Fin (2 ^ N),
      if pathEnd N gs p t = s then pathNum N gs p t else 0 := by
  induction gs generalizing s t with
  | nil =>
    simp only [ampNum, pathEnd, pathNum]
    change (if s = t then (1 : GaussianInt) else 0) =
      ∑ _ : Fin 0 → Fin (2 ^ N), if t = s then (1 : GaussianInt) else 0
    simp only [Fintype.sum_unique]
    simp only [eq_comm (a := s) (b := t)]
  | cons g gs ih =>
    simp only [ampNum, List.length_cons, pathEnd, pathNum]
    rw [sum_fun_fin_succ]
    simp only [Fin.tail_cons, Fin.cons_zero, ih, Finset.sum_mul, ite_mul, zero_mul]

private theorem gaussNorm_eq_re_mul_star (a : GaussianInt) :
    a.norm = (a * star a).re := by
  have h := Zsqrtd.norm_eq_mul_conj a
  have h2 := congrArg Zsqrtd.re h
  simpa [Zsqrtd.re_intCast] using h2

private theorem gaussReSumFinset {ι : Type*}
    (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Zsqrtd.re_add, ih]

private theorem gaussReSum {ι : Type*} [Fintype ι]
    (f : ι → GaussianInt) :
    (∑ i, f i).re = ∑ i, (f i).re :=
  gaussReSumFinset Finset.univ f

private theorem iteMulStarRe (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (a b : GaussianInt) :
    (((if c1 then a else 0) * star (if c2 then b else 0) : GaussianInt).re)
      = (if c1 then (if c2 then (a * star b).re else 0) else 0) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp [h1, h2]

private theorem ampNormExpand (N : ℕ) (gs : List QGate)
    (s : Fin (2 ^ N)) (t : Fin (2 ^ N)) :
    (ampNum N gs s t).norm
      = ∑ p, ∑ q, if pathEnd N gs p t = s then
          (if pathEnd N gs q t = s then
            (pathNum N gs p t * star (pathNum N gs q t)).re else 0)
        else 0 := by
  rw [ampNum_eq_sum_pathNum, gaussNorm_eq_re_mul_star]
  rw [star_sum]
  rw [Fintype.sum_mul_sum]
  rw [gaussReSum]
  apply Finset.sum_congr rfl
  intro p _
  rw [gaussReSum]
  apply Finset.sum_congr rfl
  intro q _
  exact iteMulStarRe _ _ _ _

/-- **Gap as a signed sum of squared moduli.** For every circuit `gs` and input index `t`, the
path-pair gap is the sum over basis states `s` of the output sign of `s` times the squared modulus
`re ^ 2 + im ^ 2` (`GaussianInt.norm`) of the cleared amplitude `ampNum N gs s t`. -/
theorem pathPairGap_eq_sum_outSign_norm (N : ℕ) (gs : List QGate) (t : Fin (2 ^ N)) :
    pathPairGap N gs t = ∑ s : Fin (2 ^ N), outSign s * (ampNum N gs s t).norm := by
  unfold pathPairGap
  have hpush : ∀ s : Fin (2 ^ N), outSign s * (ampNum N gs s t).norm
      = ∑ p, ∑ q, outSign s * (if pathEnd N gs p t = s then
          (if pathEnd N gs q t = s then
            (pathNum N gs p t * star (pathNum N gs q t)).re else 0)
        else 0) := by
    intro s
    rw [ampNormExpand N gs s t]
    simp only [Finset.mul_sum]
  simp only [hpush]
  conv => rhs; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  have hcollapse : ∀ s : Fin (2 ^ N), outSign s * (if pathEnd N gs p t = s then
        (if pathEnd N gs q t = s then
          (pathNum N gs p t * star (pathNum N gs q t)).re else 0)
      else 0)
      = if pathEnd N gs p t = s then
        (if pathEnd N gs q t = s then
          outSign s * (pathNum N gs p t * star (pathNum N gs q t)).re else 0)
      else 0 := by
    intro s
    by_cases h1 : pathEnd N gs p t = s
    · by_cases h2 : pathEnd N gs q t = s <;> simp [h1, h2]
    · simp [h1]
  simp only [hcollapse]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  by_cases h : pathEnd N gs p t = pathEnd N gs q t
  · have hQ : pathEnd N gs q t = pathEnd N gs p t := h.symm
    rw [ite_eq_left h, ite_eq_left hQ]
  · have hQ : ¬ pathEnd N gs q t = pathEnd N gs p t := fun hh => h hh.symm
    rw [ite_eq_right h, ite_eq_right hQ]

private theorem starRingEnd_mul_self_re (z : ℂ) :
    (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [mul_comm (starRingEnd ℂ z) z, Complex.mul_conj, Complex.ofReal_re]

private theorem scaled_normSq_eq_norm {N : ℕ} {gs : List QGate}
    (s t : Fin (2 ^ N)) :
    ((gs.map gateDenom).prod : ℝ) ^ 2 * Complex.normSq (ampSum N gs s t) =
      (((ampNum N gs s t).norm : ℤ) : ℝ) := by
  have hmul := ampNum_eq_ampSum_mul (N := N) (gs := gs) s t
  have hns : Complex.normSq ((ampNum N gs s t : GaussianInt) : ℂ) =
      Complex.normSq (ampSum N gs s t) *
        ((((gs.map gateDenom).prod : ℕ) : ℝ) ^ 2) := by
    rw [hmul, Complex.normSq_mul, Complex.normSq_natCast]
    ring
  have hnorm : (((ampNum N gs s t).norm : ℤ) : ℝ) =
      Complex.normSq ((ampNum N gs s t : GaussianInt) : ℂ) :=
    GaussianInt.intCast_real_norm _
  rw [hnorm, hns]
  ring

private theorem bqpInitState_eq_ite_index (x : List Bool) (a : ℕ)
    (s : Fin (2 ^ (x.length + a))) :
    bqpInitState x a s = if s = bqpInitIndex x a then 1 else 0 := by
  have hlt : qNumOf x < 2 ^ x.length := by
    have h := qNumOf_lt_two_pow_add x 0
    rwa [Nat.add_zero] at h
  have hval : ∀ t : Fin (2 ^ (x.length + a)),
      (t.val % 2 ^ x.length = qNumOf x ∧ t.val / 2 ^ x.length = 0) ↔
        t = bqpInitIndex x a := by
    intro t
    constructor
    · intro hcon
      apply Fin.ext
      have hdm := Nat.div_add_mod t.val (2 ^ x.length)
      rw [hcon.1, hcon.2, mul_zero, zero_add] at hdm
      exact hdm.symm
    · intro h
      have hv : t.val = qNumOf x := Fin.ext_iff.mp h
      constructor
      · rw [hv]
        exact Nat.mod_eq_of_lt hlt
      · rw [hv]
        exact Nat.div_eq_zero_iff.mpr (Or.inr hlt)
  change (if s.val % 2 ^ x.length = qNumOf x then (1 : ℂ) else 0) *
      (if s.val / 2 ^ x.length = 0 then 1 else 0) =
    if s = bqpInitIndex x a then 1 else 0
  by_cases h1 : s.val % 2 ^ x.length = qNumOf x
  · by_cases h2 : s.val / 2 ^ x.length = 0
    · have hs : s = bqpInitIndex x a := (hval s).mp ⟨h1, h2⟩
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left hs, mul_one]
    · have hs : s ≠ bqpInitIndex x a := fun h => h2 ((hval s).mpr h).2
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right hs, mul_zero]
  · have hs : s ≠ bqpInitIndex x a := fun h => h1 ((hval s).mpr h).1
    rw [ite_eq_right h1, ite_eq_right hs, zero_mul]

private theorem applyCircuit_bqpInitState_eq_ampSum {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) (s : Fin (2 ^ (x.length + a))) :
    applyCircuit (x.length + a) gs (bqpInitState x a) s =
      ampSum (x.length + a) gs s (bqpInitIndex x a) := by
  rw [applyCircuit_eq_ampSum hgs]
  simp_rw [bqpInitState_eq_ite_index, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- **Explicit scaled acceptance.** For a circuit `gs` of well-formed gates (unitary 2-local
gates, `QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the squared product of
the gate denominators times the acceptance probability equals the accepting cleared weight
`accWeight` for paths from the initial index `bqpInitIndex x a`. This is the explicit form of
`acceptProb_scaled_nat`. -/
theorem acceptProb_scaled_eq_accWeight {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    ((gs.map gateDenom).prod : ℝ) ^ 2 *
        acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) =
      (accWeight (x.length + a) gs (bqpInitIndex x a) : ℝ) := by
  unfold acceptProb accWeight
  rw [Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [applyCircuit_bqpInitState_eq_ampSum x a hgs s]
  split_ifs with h
  · rw [starRingEnd_mul_self_re]
    exact scaled_normSq_eq_norm s (bqpInitIndex x a)
  · simp

private theorem sum_norm_ampNum_bqpInitIndex {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    ∑ s : Fin (2 ^ (x.length + a)), (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm =
      ((gs.map gateDenom).prod : ℤ) ^ 2 := by
  have hsum : ((gs.map gateDenom).prod : ℝ) ^ 2 *
      sqNorm (applyCircuit (x.length + a) gs (bqpInitState x a)) =
      ((∑ s : Fin (2 ^ (x.length + a)),
        (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm : ℤ) : ℝ) := by
    unfold sqNorm
    rw [Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [applyCircuit_bqpInitState_eq_ampSum x a hgs s, starRingEnd_mul_self_re]
    exact scaled_normSq_eq_norm s (bqpInitIndex x a)
  rw [sqNorm_applyCircuit hgs, sqNorm_bqpInitState, mul_one] at hsum
  have h2 : ((∑ s : Fin (2 ^ (x.length + a)),
      (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm : ℤ) : ℝ) =
      ((((gs.map gateDenom).prod : ℤ) ^ 2 : ℤ) : ℝ) := by
    rw [← hsum]
    simp only [Int.cast_pow, Int.cast_natCast]
  exact_mod_cast h2

/-- **Integer gap identity.** For a circuit `gs` of well-formed gates (unitary 2-local gates,
`QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the path-pair gap for paths
from the initial index `bqpInitIndex x a` equals twice the accepting cleared weight minus the
squared product of the gate denominators. By unitarity, that square is the total cleared
weight. -/
theorem pathPairGap_eq_two_mul_accWeight_sub {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    pathPairGap (x.length + a) gs (bqpInitIndex x a) =
      2 * accWeight (x.length + a) gs (bqpInitIndex x a) - ((gs.map gateDenom).prod : ℤ) ^ 2 := by
  rw [pathPairGap_eq_sum_outSign_norm]
  have hterm : ∀ s : Fin (2 ^ (x.length + a)),
      outSign s * (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm =
        2 * (if qBit 0 s.val = 1
          then (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm else 0) -
          (ampNum (x.length + a) gs s (bqpInitIndex x a)).norm := by
    intro s
    simp only [outSign]
    split_ifs with h <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_norm_ampNum_bqpInitIndex _ _ hgs,
    accWeight]

/-- **Gap and acceptance probability.** For a circuit `gs` of well-formed gates (unitary 2-local
gates, `QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the path-pair gap for
paths from the initial index `bqpInitIndex x a` equals the squared product of the gate
denominators times `2 * acceptProb - 1`. -/
theorem pathPairGap_eq {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    (pathPairGap (x.length + a) gs (bqpInitIndex x a) : ℝ) =
      ((gs.map gateDenom).prod : ℝ) ^ 2 *
        (2 * acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) - 1) := by
  have h1 := pathPairGap_eq_two_mul_accWeight_sub _ _ hgs
  have h2 := acceptProb_scaled_eq_accWeight _ _ hgs
  have h1r : (pathPairGap (x.length + a) gs (bqpInitIndex x a) : ℝ) =
      2 * (accWeight (x.length + a) gs (bqpInitIndex x a) : ℝ) -
        ((((gs.map gateDenom).prod : ℤ) ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h1
  have hPC : ((((gs.map gateDenom).prod : ℤ) ^ 2 : ℤ) : ℝ) =
      ((gs.map gateDenom).prod : ℝ) ^ 2 := by
    norm_cast
  rw [h1r, hPC, ← h2]
  ring

/-- **Sign lemma.** For a circuit `gs` of well-formed gates (unitary 2-local gates,
`QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the path-pair gap for paths
from the initial index `bqpInitIndex x a` has the sign of the acceptance probability minus
`1 / 2`. -/
theorem sign_pathPairGap {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    SignType.sign (pathPairGap (x.length + a) gs (bqpInitIndex x a)) =
      SignType.sign (acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) - 1 / 2) := by
  have hreal := pathPairGap_eq _ _ hgs
  have hDpos : (0 : ℝ) < ((gs.map gateDenom).prod : ℝ) := by
    have h : 0 < (gs.map gateDenom).prod :=
      List.prod_pos (fun a ha => by
        obtain ⟨g, -, rfl⟩ := List.mem_map.mp ha
        exact gateDenom_pos g)
    exact_mod_cast h
  have hCpos : (0 : ℝ) < 2 * (((gs.map gateDenom).prod : ℝ) ^ 2) := by positivity
  have hcast : ((pathPairGap (x.length + a) gs (bqpInitIndex x a) : ℤ) : ℝ) =
      (2 * (((gs.map gateDenom).prod : ℝ) ^ 2)) *
        (acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) - 1 / 2) := by
    rw [hreal]
    ring
  calc SignType.sign (pathPairGap (x.length + a) gs (bqpInitIndex x a))
      = SignType.sign (((pathPairGap (x.length + a) gs
          (bqpInitIndex x a) : ℤ) : ℝ)) := by
        rw [sign_intCast]
    _ = SignType.sign (2 * (((gs.map gateDenom).prod : ℝ) ^ 2)) *
          SignType.sign (acceptProb (applyCircuit (x.length + a) gs
            (bqpInitState x a)) - 1 / 2) := by
        rw [hcast, sign_mul]
    _ = SignType.sign (acceptProb (applyCircuit (x.length + a) gs
          (bqpInitState x a)) - 1 / 2) := by
        rw [sign_pos hCpos, one_mul]

/-- **Positive gap and acceptance above one half.** For a circuit `gs` of well-formed gates
(unitary 2-local gates, `QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the
path-pair gap for paths from the initial index `bqpInitIndex x a` is positive exactly when the
acceptance probability exceeds `1 / 2`. -/
theorem pathPairGap_pos_iff {gs : List QGate} (x : List Bool) (a : ℕ)
    (hgs : ∀ g ∈ gs, QGateWellFormed (x.length + a) g) :
    0 < pathPairGap (x.length + a) gs (bqpInitIndex x a) ↔
      1 / 2 < acceptProb (applyCircuit (x.length + a) gs (bqpInitState x a)) := by
  have hreal := pathPairGap_eq _ _ hgs
  have hD : (0 : ℝ) < (((gs.map gateDenom).prod : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) < ((gs.map gateDenom).prod : ℝ) := by
      have h : 0 < (gs.map gateDenom).prod :=
        List.prod_pos (fun a ha => by
          obtain ⟨g, -, rfl⟩ := List.mem_map.mp ha
          exact gateDenom_pos g)
      exact_mod_cast h
    positivity
  rw [← Int.cast_pos (R := ℝ), hreal, mul_pos_iff_of_pos_left hD]
  constructor <;> intro h <;> linarith

/-- **BQP form of the sign lemma.** Every language `L` in `BQP` has a polynomial-time computable
family of circuits of well-formed gates (unitary 2-local gates, `QGateWellFormed`), with
polynomially many ancilla qubits and gates, such that for every input `x` the path-pair gap of
the circuit for `x`, for paths from the initial index of `x`, is positive exactly when `L x` is
true. -/
theorem exists_pathPairGap_of_mem_BQP {L : List Bool → Bool} (hL : L ∈ BQP) :
    ∃ a s : Polynomial ℕ, ∃ gates : List Bool → List QGate,
      IsPolyTime gates ∧
      (∀ x, (gates x).length ≤ s.eval x.length) ∧
      (∀ x, ∀ g ∈ gates x, QGateWellFormed (x.length + a.eval x.length) g) ∧
      ∀ x, (L x = true ↔
        0 < pathPairGap (x.length + a.eval x.length) (gates x)
          (bqpInitIndex x (a.eval x.length))) := by
  rw [mem_BQP_iff] at hL
  obtain ⟨a, s, gates, hpoly, hlen, hwf, hbounds⟩ := hL
  refine ⟨a, s, gates, hpoly, hlen, hwf, fun x => ?_⟩
  have hpos := pathPairGap_pos_iff (gs := gates x) (x := x) (a := a.eval x.length) (hwf x)
  obtain ⟨hT, hF⟩ := hbounds x
  constructor
  · intro hTx
    rw [hpos]
    have hge := hT hTx
    linarith
  · intro hgap
    cases hLx : L x
    · exfalso
      rw [hpos] at hgap
      have hle := hF hLx
      linarith
    · rfl

end Cslib.Complexity.Classes
