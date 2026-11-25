/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Circuit semantics: unitarity, norm preservation, Born-probability range

For a well-formed 2-local gate `g` on `N` qubits, `applyGate N g` is the
`mulVec` action of an explicit unitary matrix `gateMatrix N g`: its entry at
`(s, t)` is the gate-matrix entry between the two-qubit components of `s` and
`t` when `s` and `t` agree on every qubit outside the gate, and `0` otherwise.
Hence circuits of well-formed gates preserve `sqNorm`, the BQP initial state
is a unit vector, and `acceptProb` of a unit vector lies in `[0, 1]`.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapters 2 and 4.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

/-- The `2^N × 2^N` matrix of a 2-local gate: entry `(s, t)` is the encoded
gate-matrix entry between the `(i, j)`-bit pairs of `s` and `t` when `s` and
`t` agree at every qubit other than `i` and `j`, and `0` otherwise. -/
noncomputable def gateMatrix (N : ℕ) (g : QGate) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  fun s t =>
    if (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
        qBit k.val s.val = qBit k.val t.val) then
      matrixOfEntries g.2.2 (qBit g.1 s.val, qBit g.2.1 s.val)
        (qBit g.1 t.val, qBit g.2.1 t.val)
    else 0

private theorem conj_mul_self_re_eq_normSq (z : ℂ) :
    (starRingEnd ℂ z * z).re = Complex.normSq z := by
  have h2 : starRingEnd ℂ z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self]
  rw [h2, Complex.ofReal_re]

private theorem conj_mul_self_re_nonneg (z : ℂ) :
    0 ≤ (starRingEnd ℂ z * z).re := by
  rw [conj_mul_self_re_eq_normSq]
  exact Complex.normSq_nonneg z

private theorem qNumOf_lt_pow (x : List Bool) : qNumOf x < 2 ^ x.length := by
  induction x with
  | nil => simp [qNumOf]
  | cons hd tl ih =>
    simp only [qNumOf, List.length_cons, pow_succ]
    cases hd <;> simp <;> omega

private theorem conj_mul_prod_re (a b : ℂ) :
    (starRingEnd ℂ (a * b) * (a * b)).re =
    (starRingEnd ℂ a * a).re * (starRingEnd ℂ b * b).re := by
  have hmul : starRingEnd ℂ (a * b) = starRingEnd ℂ a * starRingEnd ℂ b :=
    map_mul _ _ _
  have hring : starRingEnd ℂ (a * b) * (a * b) =
      (starRingEnd ℂ a * a) * (starRingEnd ℂ b * b) := by
    rw [hmul]; ring
  have hnorm : ∀ z : ℂ, starRingEnd ℂ z * z = ((Complex.normSq z : ℝ) : ℂ) :=
    fun z => by rw [← Complex.normSq_eq_conj_mul_self]
  rw [hring, hnorm, hnorm, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

private theorem gm_div_add_pow_mul (y D k M : ℕ) :
    (y + D * (2 ^ k * M)) / 2 ^ k = y / 2 ^ k + D * M := by
  have h : D * (2 ^ k * M) = 2 ^ k * (D * M) := by ring
  rw [h]
  exact Nat.add_mul_div_left _ _ (by positivity)

private theorem gm_add_even_mod_two (x E : ℕ) (hE : 2 ∣ E) :
    (x + E) % 2 = x % 2 := by
  obtain ⟨E', hE⟩ := hE
  omega

private theorem gm_qBit_mod_pow (V N k : ℕ) (hk : k < N) :
    ((V % 2 ^ N) / 2 ^ k) % 2 = (V / 2 ^ k) % 2 := by
  have h2N : (2 : ℕ) ^ N = 2 ^ k * 2 ^ (N - k) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hk)]
  have hV : V = V % 2 ^ N + (V / 2 ^ N) * (2 ^ k * 2 ^ (N - k)) := by
    have h2 : (V / 2 ^ N) * (2 ^ k * 2 ^ (N - k)) = 2 ^ N * (V / 2 ^ N) := by
      rw [h2N]; ring
    rw [h2]
    exact (Nat.mod_add_div V (2 ^ N)).symm
  have hM : (2 : ℕ) ∣ 2 ^ (N - k) := by
    have h := pow_dvd_pow (2 : ℕ) (show 1 ≤ N - k by omega)
    simpa using h
  have hDM : (2 : ℕ) ∣ (V / 2 ^ N) * 2 ^ (N - k) := by
    obtain ⟨M', hM'⟩ := hM
    exact ⟨(V / 2 ^ N) * M', by rw [hM']; ring⟩
  have hdiv : V / 2 ^ k = (V % 2 ^ N) / 2 ^ k + (V / 2 ^ N) * 2 ^ (N - k) := by
    conv_lhs => rw [hV]
    exact gm_div_add_pow_mul _ _ _ _
  rw [hdiv]
  exact (gm_add_even_mod_two _ _ hDM).symm

private theorem gm_singleBit_decomp (s i : ℕ) :
    s % 2 ^ i < 2 ^ i ∧
      s = s % 2 ^ i + (qBit i s).val * 2 ^ i + ((s / 2 ^ i) / 2) * 2 ^ (i + 1) := by
  refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
  have hs : s = s % 2 ^ i + 2 ^ i * (s / 2 ^ i) := (Nat.mod_add_div s (2 ^ i)).symm
  have hQ : s / 2 ^ i = (qBit i s).val + 2 * ((s / 2 ^ i) / 2) :=
    (Nat.mod_add_div (s / 2 ^ i) 2).symm
  rw [hQ] at hs
  rw [show (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i from pow_succ' 2 i]
  linear_combination hs

private theorem gm_even_add_pow (X Y e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    (2 : ℕ) ∣ X * 2 ^ e + Y * 2 ^ f := by
  have e1 : (2 : ℕ) ∣ 2 ^ e := by
    have h := pow_dvd_pow (2 : ℕ) he
    simpa using h
  have e2 : (2 : ℕ) ∣ 2 ^ f := by
    have h := pow_dvd_pow (2 : ℕ) hf
    simpa using h
  obtain ⟨u, hu⟩ := e1
  obtain ⟨v, hv⟩ := e2
  exact ⟨X * u + Y * v, by rw [hu, hv]; ring⟩

private theorem gm_add_mul_pow_lt (L b i : ℕ) (hL : L < 2 ^ i) (hb : b < 2) :
    L + b * 2 ^ i < 2 ^ (i + 1) := by
  have hpow : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases hb01 with rfl | rfl
  · rw [zero_mul, add_zero]; omega
  · rw [one_mul]; omega

private theorem gm_qBit_singleBit_eq (s i : ℕ) (b : ℕ) (hb : b < 2) :
    ((s - (qBit i s).val * 2 ^ i + b * 2 ^ i) / 2 ^ i) % 2 = b := by
  obtain ⟨hL, hs⟩ := gm_singleBit_decomp s i
  set L := s % 2 ^ i
  set H := (s / 2 ^ i) / 2
  have hsub : s - (qBit i s).val * 2 ^ i = L + H * 2 ^ (i + 1) := by omega
  have hV : s - (qBit i s).val * 2 ^ i + b * 2 ^ i = L + 2 ^ i * (b + H * 2) := by
    rw [hsub, show (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i from pow_succ' 2 i]
    ring
  rw [hV, Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 2 ^ i),
    Nat.div_eq_of_lt hL]
  omega

private theorem gm_qBit_singleBit_ne (s i k : ℕ) (b : ℕ) (hb : b < 2) (hk : k ≠ i) :
    ((s - (qBit i s).val * 2 ^ i + b * 2 ^ i) / 2 ^ k) % 2 = (s / 2 ^ k) % 2 := by
  obtain ⟨hL, hs⟩ := gm_singleBit_decomp s i
  set L := s % 2 ^ i
  set H := (s / 2 ^ i) / 2
  have hsub : s - (qBit i s).val * 2 ^ i = L + H * 2 ^ (i + 1) := by omega
  rcases lt_or_gt_of_ne hk with hki | hik
  · have h2i : (2 : ℕ) ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hki)]
    have h2i1 : (2 : ℕ) ^ (i + 1) = 2 ^ k * 2 ^ (i + 1 - k) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k ≤ i + 1)]
    have hV1 : s - (qBit i s).val * 2 ^ i + b * 2 ^ i
        = L + 2 ^ k * (H * 2 ^ (i + 1 - k) + b * 2 ^ (i - k)) := by
      rw [hsub, h2i, h2i1]; ring
    have hs2 : s
        = L + 2 ^ k * ((qBit i s).val * 2 ^ (i - k) + H * 2 ^ (i + 1 - k)) := by
      conv_lhs => rw [hs]
      rw [h2i, h2i1]; ring
    have eV : ((s - (qBit i s).val * 2 ^ i + b * 2 ^ i) / 2 ^ k) % 2
        = (L / 2 ^ k) % 2 := by
      rw [hV1, Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 2 ^ k)]
      exact gm_add_even_mod_two _ _ (gm_even_add_pow _ _ _ _ (by omega) (by omega))
    have eS : (s / 2 ^ k) % 2 = (L / 2 ^ k) % 2 := by
      rw [hs2, Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 2 ^ k)]
      exact gm_add_even_mod_two _ _ (gm_even_add_pow _ _ _ _ (by omega) (by omega))
    exact eV.trans eS.symm
  · have h2k : (2 : ℕ) ^ k = 2 ^ (i + 1) * 2 ^ (k - (i + 1)) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : i + 1 ≤ k)]
    have ha : (qBit i s).val < 2 := (qBit i s).isLt
    have hV1 : s - (qBit i s).val * 2 ^ i + b * 2 ^ i
        = (L + b * 2 ^ i) + 2 ^ (i + 1) * H := by
      rw [hsub]; ring
    have hs2 : s = (L + (qBit i s).val * 2 ^ i) + 2 ^ (i + 1) * H := by
      linear_combination hs
    have e1 : (s - (qBit i s).val * 2 ^ i + b * 2 ^ i) / 2 ^ k
        = (0 + H) / 2 ^ (k - (i + 1)) := by
      rw [hV1, h2k, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 2 ^ (i + 1)),
        Nat.div_eq_of_lt (gm_add_mul_pow_lt L b i hL hb)]
    have e2 : s / 2 ^ k = (0 + H) / 2 ^ (k - (i + 1)) := by
      rw [hs2, h2k, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by positivity : (0 : ℕ) < 2 ^ (i + 1)),
        Nat.div_eq_of_lt (gm_add_mul_pow_lt L (qBit i s).val i hL ha)]
    rw [e1, e2]

private theorem gm_twoBits_le (s i j : ℕ) (hij : i < j) :
    (qBit i s).val * 2 ^ i + (qBit j s).val * 2 ^ j ≤ s := by
  obtain ⟨_, hsj⟩ := gm_singleBit_decomp s j
  obtain ⟨_, hsL⟩ := gm_singleBit_decomp (s % 2 ^ j) i
  have hbit : (qBit i (s % 2 ^ j)).val = (qBit i s).val := gm_qBit_mod_pow s j i hij
  rw [hbit] at hsL
  omega

private theorem gm_setBits_val_reassoc (s i j b1 b2 : ℕ) (hij : i < j) :
    s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j + b1 * 2 ^ i + b2 * 2 ^ j
      = (s - (qBit i s).val * 2 ^ i + b1 * 2 ^ i) - (qBit j s).val * 2 ^ j
        + b2 * 2 ^ j := by
  have hle := gm_twoBits_le s i j hij
  omega

private theorem gm_qBit_setBits_fst {N s i j : ℕ} {b : Fin 2 × Fin 2}
    (hi : i < N) (hij : i < j) :
    qBit i (setBits N s i j b).val = b.1 := by
  apply Fin.ext
  show (((s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j + b.1.val * 2 ^ i
    + b.2.val * 2 ^ j) % 2 ^ N) / 2 ^ i) % 2 = b.1.val
  rw [gm_qBit_mod_pow _ _ _ hi, gm_setBits_val_reassoc _ _ _ _ _ hij]
  have hc : (qBit j (s - (qBit i s).val * 2 ^ i + b.1.val * 2 ^ i)).val
      = (qBit j s).val :=
    gm_qBit_singleBit_ne s i j (b.1.val) b.1.isLt (by omega : j ≠ i)
  rw [← hc, gm_qBit_singleBit_ne _ _ _ _ b.2.isLt (by omega : i ≠ j),
    gm_qBit_singleBit_eq _ _ _ b.1.isLt]

private theorem gm_qBit_setBits_snd {N s i j : ℕ} {b : Fin 2 × Fin 2}
    (hj : j < N) (hij : i < j) :
    qBit j (setBits N s i j b).val = b.2 := by
  apply Fin.ext
  show (((s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j + b.1.val * 2 ^ i
    + b.2.val * 2 ^ j) % 2 ^ N) / 2 ^ j) % 2 = b.2.val
  rw [gm_qBit_mod_pow _ _ _ hj, gm_setBits_val_reassoc _ _ _ _ _ hij]
  have hc : (qBit j (s - (qBit i s).val * 2 ^ i + b.1.val * 2 ^ i)).val
      = (qBit j s).val :=
    gm_qBit_singleBit_ne s i j (b.1.val) b.1.isLt (by omega : j ≠ i)
  rw [← hc, gm_qBit_singleBit_eq _ _ _ b.2.isLt]

private theorem gm_qBit_setBits_other {N s i j : ℕ} {b : Fin 2 × Fin 2} {k : ℕ}
    (hk : k < N) (hki : k ≠ i) (hkj : k ≠ j) (hij : i < j) :
    qBit k (setBits N s i j b).val = qBit k s := by
  apply Fin.ext
  show (((s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j + b.1.val * 2 ^ i
    + b.2.val * 2 ^ j) % 2 ^ N) / 2 ^ k) % 2 = (s / 2 ^ k) % 2
  rw [gm_qBit_mod_pow _ _ _ hk, gm_setBits_val_reassoc _ _ _ _ _ hij]
  have hc : (qBit j (s - (qBit i s).val * 2 ^ i + b.1.val * 2 ^ i)).val
      = (qBit j s).val :=
    gm_qBit_singleBit_ne s i j (b.1.val) b.1.isLt (by omega : j ≠ i)
  rw [← hc, gm_qBit_singleBit_ne _ _ _ _ b.2.isLt hkj,
    gm_qBit_singleBit_ne _ _ _ _ b.1.isLt hki]

private theorem gm_bitExpansion (N s : ℕ) (hs : s < 2 ^ N) :
    s = ∑ k ∈ Finset.range N, ((s / 2 ^ k) % 2) * 2 ^ k := by
  induction N generalizing s with
  | zero =>
    rw [Finset.sum_range_zero]
    have hs1 : s < 1 := by simpa using hs
    omega
  | succ N IH =>
    have hs' : s % 2 ^ N < 2 ^ N := Nat.mod_lt _ (by positivity)
    have hIH := IH (s % 2 ^ N) hs'
    have hbits : ∀ k < N, ((s % 2 ^ N / 2 ^ k) % 2) = ((s / 2 ^ k) % 2) :=
      fun k hk => gm_qBit_mod_pow s N k hk
    have hsum : ∑ k ∈ Finset.range N, ((s / 2 ^ k) % 2) * 2 ^ k = s % 2 ^ N := by
      rw [hIH]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hbits k (Finset.mem_range.mp hk)]
    have htop : (s / 2 ^ N) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0 : ℕ) < 2 ^ N)]
      rw [← pow_succ' 2 N]
      exact hs
    have htop2 : ((s / 2 ^ N) % 2) = s / 2 ^ N := Nat.mod_eq_of_lt htop
    have hdecomp : s = s % 2 ^ N + (s / 2 ^ N) * 2 ^ N := by
      have h := Nat.mod_add_div s (2 ^ N)
      have hc : 2 ^ N * (s / 2 ^ N) = (s / 2 ^ N) * 2 ^ N := mul_comm _ _
      omega
    simp only [Finset.sum_range_succ, hsum, htop2]
    exact hdecomp

private theorem gm_eq_of_qBit_eq {N s t : ℕ} (hs : s < 2 ^ N) (ht : t < 2 ^ N)
    (h : ∀ k < N, (s / 2 ^ k) % 2 = (t / 2 ^ k) % 2) : s = t := by
  have es := gm_bitExpansion N s hs
  have et := gm_bitExpansion N t ht
  rw [es, et]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

private theorem gm_agree_iff {N s t i j : ℕ} :
    (∀ k : Fin N, k.val ≠ i → k.val ≠ j → qBit k.val s = qBit k.val t)
      ↔ (∀ k : ℕ, k < N → k ≠ i → k ≠ j → qBit k s = qBit k t) := by
  constructor
  · intro h k hk hki hkj
    exact h ⟨k, hk⟩ hki hkj
  · intro h k hki hkj
    exact h k.val k.isLt hki hkj

private theorem gm_eq_setBits_of_agree {N s t i j : ℕ}
    (ht : t < 2 ^ N) (hi : i < N) (hj : j < N) (hij : i < j)
    (h : ∀ k : ℕ, k < N → k ≠ i → k ≠ j → qBit k s = qBit k t) :
    t = (setBits N s i j (qBit i t, qBit j t)).val := by
  apply gm_eq_of_qBit_eq ht (setBits N s i j (qBit i t, qBit j t)).isLt
  intro k hk
  by_cases hki : k = i
  · rw [hki]
    exact congrArg Fin.val
      (gm_qBit_setBits_fst (b := (qBit i t, qBit j t)) hi hij).symm
  · by_cases hkj : k = j
    · rw [hkj]
      exact congrArg Fin.val
        (gm_qBit_setBits_snd (b := (qBit i t, qBit j t)) hj hij).symm
    · exact congrArg Fin.val
        ((h k hk hki hkj).symm.trans
          (gm_qBit_setBits_other (b := (qBit i t, qBit j t)) hk hki hkj hij).symm)

private theorem gm_setBits_injective {N s i j : ℕ} (hi : i < N) (hj : j < N)
    (hij : i < j) :
    Function.Injective (setBits N s i j) := by
  intro b b' hbb
  have hval : (setBits N s i j b).val = (setBits N s i j b').val :=
    congrArg Fin.val hbb
  have e1 : b.1 = b'.1 := by
    have h1 : qBit i (setBits N s i j b).val = b.1 :=
      gm_qBit_setBits_fst (b := b) hi hij
    have h2 : qBit i (setBits N s i j b').val = b'.1 :=
      gm_qBit_setBits_fst (b := b') hi hij
    rw [hval] at h1
    rw [h2] at h1
    exact h1.symm
  have e2 : b.2 = b'.2 := by
    have h1 : qBit j (setBits N s i j b).val = b.2 :=
      gm_qBit_setBits_snd (b := b) hj hij
    have h2 : qBit j (setBits N s i j b').val = b'.2 :=
      gm_qBit_setBits_snd (b := b') hj hij
    rw [hval] at h1
    rw [h2] at h1
    exact h1.symm
  exact Prod.ext e1 e2

private theorem gm_gateMatrix_apply {N : ℕ} {g : QGate} (s t : Fin (2 ^ N)) :
    (gateMatrix N g) s t
      = if (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
          qBit k.val s.val = qBit k.val t.val)
        then (matrixOfEntries g.2.2) (qBit g.1 s.val, qBit g.2.1 s.val)
          (qBit g.1 t.val, qBit g.2.1 t.val)
        else 0 := rfl

/-- Applying a well-formed gate is multiplication by its gate matrix. -/
theorem applyGate_eq_gateMatrix_mulVec {N : ℕ} {g : QGate}
    (hg : QGateWellFormed N g) (ψ : Fin (2 ^ N) → ℂ) :
    applyGate N g ψ = Matrix.mulVec (gateMatrix N g) ψ := by
  obtain ⟨hij, hjN, _⟩ := hg
  have hiN : g.1 < N := lt_trans hij hjN
  funext s
  show (∑ b : Fin 2 × Fin 2, (matrixOfEntries g.2.2)
        (qBit g.1 s.val, qBit g.2.1 s.val) b *
        ψ (setBits N s.val g.1 g.2.1 b))
      = ∑ t : Fin (2 ^ N), (gateMatrix N g) s t * ψ t
  trans ∑ t ∈ Finset.univ.filter
      (fun t => ∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
        qBit k.val s.val = qBit k.val t.val),
    (gateMatrix N g) s t * ψ t
  · refine Finset.sum_bij (fun b _ => setBits N s.val g.1 g.2.1 b) ?_ ?_ ?_ ?_
    · intro b hb
      show setBits N s.val g.1 g.2.1 b ∈ Finset.univ.filter _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [gm_agree_iff]
      intro k hk hki hkj
      exact (gm_qBit_setBits_other hk hki hkj hij).symm
    · intro b1 _ b2 _ h12
      exact gm_setBits_injective hiN hjN hij h12
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [gm_agree_iff] at ht
      refine ⟨(qBit g.1 t.val, qBit g.2.1 t.val), Finset.mem_univ _, ?_⟩
      show setBits N s.val g.1 g.2.1 (qBit g.1 t.val, qBit g.2.1 t.val) = t
      have htw := gm_eq_setBits_of_agree t.isLt hiN hjN hij ht
      exact Fin.ext htw.symm
    · intro b hb
      obtain ⟨b1, b2⟩ := b
      show (matrixOfEntries g.2.2) (qBit g.1 s.val, qBit g.2.1 s.val) (b1, b2) *
          ψ (setBits N s.val g.1 g.2.1 (b1, b2))
        = (gateMatrix N g) s (setBits N s.val g.1 g.2.1 (b1, b2)) *
          ψ (setBits N s.val g.1 g.2.1 (b1, b2))
      rw [gm_gateMatrix_apply]
      have hag : ∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
          qBit k.val s.val
            = qBit k.val (setBits N s.val g.1 g.2.1 (b1, b2)).val := by
        rw [gm_agree_iff]
        intro k hk hki hkj
        exact (gm_qBit_setBits_other hk hki hkj hij).symm
      rw [ite_eq_left hag]
      have hA : qBit g.1 (setBits N s.val g.1 g.2.1 (b1, b2)).val = b1 :=
        gm_qBit_setBits_fst hiN hij
      have hB : qBit g.2.1 (setBits N s.val g.1 g.2.1 (b1, b2)).val = b2 :=
        gm_qBit_setBits_snd hjN hij
      rw [hA, hB]
  · apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t _ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    show (gateMatrix N g) s t * ψ t = 0
    rw [gm_gateMatrix_apply, ite_eq_right ht, zero_mul]

/-- The gate matrix of a well-formed gate is unitary. -/
theorem gateMatrix_mem_unitaryGroup {N : ℕ} {g : QGate}
    (hg : QGateWellFormed N g) :
    gateMatrix N g ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  obtain ⟨hij, hjN, hU⟩ := hg
  have hiN : g.1 < N := lt_trans hij hjN
  rw [Matrix.mem_unitaryGroup_iff']
  apply Matrix.ext
  intro t t'
  rw [Matrix.mul_apply]
  have hstar : ∀ s : Fin (2 ^ N),
      (star (gateMatrix N g)) t s = star ((gateMatrix N g) s t) := by
    intro s
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.conjTranspose_apply _ _ _
  simp only [hstar]
  rw [Matrix.one_apply]
  by_cases hoff : ∀ k : ℕ, k < N → k ≠ g.1 → k ≠ g.2.1 →
    qBit k t.val = qBit k t'.val
  · have hvanish : ∀ s ∈ (Finset.univ : Finset (Fin (2 ^ N))),
        s ∉ Finset.univ.filter (fun s =>
          (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
            qBit k.val s.val = qBit k.val t.val) ∧
          (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
            qBit k.val s.val = qBit k.val t'.val)) →
        star ((gateMatrix N g) s t) * (gateMatrix N g) s t' = 0 := by
      intro s _ hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [gm_gateMatrix_apply s t, gm_gateMatrix_apply s t']
      by_cases h1 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
        qBit k.val s.val = qBit k.val t.val)
      · by_cases h2 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
          qBit k.val s.val = qBit k.val t'.val)
        · exact absurd ⟨h1, h2⟩ hs
        · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, star_zero, zero_mul]
    rw [(Finset.sum_subset (Finset.filter_subset _ _) hvanish).symm]
    trans ∑ p : Fin 2 × Fin 2,
      star ((matrixOfEntries g.2.2) p (qBit g.1 t.val, qBit g.2.1 t.val)) *
        (matrixOfEntries g.2.2) p (qBit g.1 t'.val, qBit g.2.1 t'.val)
    · symm
      refine Finset.sum_bij (fun p _ => setBits N t.val g.1 g.2.1 p) ?_ ?_ ?_ ?_
      · intro p hp
        show setBits N t.val g.1 g.2.1 p ∈ Finset.univ.filter _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rw [gm_agree_iff]
          intro k hk hki hkj
          exact gm_qBit_setBits_other hk hki hkj hij
        · rw [gm_agree_iff]
          intro k hk hki hkj
          exact (gm_qBit_setBits_other hk hki hkj hij).trans (hoff k hk hki hkj)
      · intro b1 _ b2 _ h12
        exact gm_setBits_injective hiN hjN hij h12
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have h1 := hs.1
        rw [gm_agree_iff] at h1
        refine ⟨(qBit g.1 s.val, qBit g.2.1 s.val), Finset.mem_univ _, ?_⟩
        show setBits N t.val g.1 g.2.1 (qBit g.1 s.val, qBit g.2.1 s.val) = s
        have hsw := gm_eq_setBits_of_agree s.isLt hiN hjN hij
          (fun k hk hki hkj => (h1 k hk hki hkj).symm)
        exact Fin.ext hsw.symm
      · intro p hp
        obtain ⟨p1, p2⟩ := p
        show star ((matrixOfEntries g.2.2) (p1, p2)
              (qBit g.1 t.val, qBit g.2.1 t.val)) *
            (matrixOfEntries g.2.2) (p1, p2)
              (qBit g.1 t'.val, qBit g.2.1 t'.val)
          = star ((gateMatrix N g)
              (setBits N t.val g.1 g.2.1 (p1, p2)) t) *
            (gateMatrix N g) (setBits N t.val g.1 g.2.1 (p1, p2)) t'
        rw [gm_gateMatrix_apply _ t, gm_gateMatrix_apply _ t']
        have hag1 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
            qBit k.val (setBits N t.val g.1 g.2.1 (p1, p2)).val
              = qBit k.val t.val) := by
          rw [gm_agree_iff]
          intro k hk hki hkj
          exact gm_qBit_setBits_other hk hki hkj hij
        have hag2 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
            qBit k.val (setBits N t.val g.1 g.2.1 (p1, p2)).val
              = qBit k.val t'.val) := by
          rw [gm_agree_iff]
          intro k hk hki hkj
          exact (gm_qBit_setBits_other hk hki hkj hij).trans (hoff k hk hki hkj)
        rw [ite_eq_left hag1, ite_eq_left hag2]
        have hA : qBit g.1 (setBits N t.val g.1 g.2.1 (p1, p2)).val = p1 :=
          gm_qBit_setBits_fst hiN hij
        have hB : qBit g.2.1 (setBits N t.val g.1 g.2.1 (p1, p2)).val = p2 :=
          gm_qBit_setBits_snd hjN hij
        rw [hA, hB]
    · have hgram : (∑ p : Fin 2 × Fin 2,
          star ((matrixOfEntries g.2.2) p (qBit g.1 t.val, qBit g.2.1 t.val)) *
            (matrixOfEntries g.2.2) p (qBit g.1 t'.val, qBit g.2.1 t'.val))
          = (star (matrixOfEntries g.2.2) * (matrixOfEntries g.2.2))
            (qBit g.1 t.val, qBit g.2.1 t.val)
            (qBit g.1 t'.val, qBit g.2.1 t'.val) := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro p hp
        have hsp : (star (matrixOfEntries g.2.2))
            (qBit g.1 t.val, qBit g.2.1 t.val) p
            = star ((matrixOfEntries g.2.2) p
              (qBit g.1 t.val, qBit g.2.1 t.val)) := by
          rw [Matrix.star_eq_conjTranspose]
          exact Matrix.conjTranspose_apply _ _ _
        rw [hsp]
      rw [hgram, hU, Matrix.one_apply]
      by_cases htt : t = t'
      · rw [ite_eq_left htt]
        have hat : (qBit g.1 t.val, qBit g.2.1 t.val)
            = (qBit g.1 t'.val, qBit g.2.1 t'.val) := by rw [htt]
        rw [ite_eq_left hat]
      · rw [ite_eq_right htt]
        have hat : (qBit g.1 t.val, qBit g.2.1 t.val)
            ≠ (qBit g.1 t'.val, qBit g.2.1 t'.val) := by
          intro hcon
          apply htt
          apply Fin.ext
          apply gm_eq_of_qBit_eq t.isLt t'.isLt
          intro k hk
          by_cases hki : k = g.1
          · rw [hki]
            simp only [Prod.mk.injEq] at hcon
            exact congrArg Fin.val hcon.1
          · by_cases hkj : k = g.2.1
            · rw [hkj]
              simp only [Prod.mk.injEq] at hcon
              exact congrArg Fin.val hcon.2
            · exact congrArg Fin.val (hoff k hk hki hkj)
        rw [ite_eq_right hat]
  · push Not at hoff
    obtain ⟨k, hkN, hki, hkj, hkk⟩ := hoff
    have hsum0 : ∑ s : Fin (2 ^ N),
        star ((gateMatrix N g) s t) * (gateMatrix N g) s t' = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      show star ((gateMatrix N g) s t) * (gateMatrix N g) s t' = 0
      rw [gm_gateMatrix_apply s t, gm_gateMatrix_apply s t']
      by_cases h1 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
        qBit k.val s.val = qBit k.val t.val)
      · by_cases h2 : (∀ k : Fin N, k.val ≠ g.1 → k.val ≠ g.2.1 →
          qBit k.val s.val = qBit k.val t'.val)
        · exfalso
          apply hkk
          exact (h1 ⟨k, hkN⟩ hki hkj).symm.trans (h2 ⟨k, hkN⟩ hki hkj)
        · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, star_zero, zero_mul]
    rw [hsum0]
    have htt : t ≠ t' := by
      intro hcon
      apply hkk
      rw [hcon]
    rw [ite_eq_right htt]

private theorem sqNorm_mulVec_unitary {N : ℕ}
    {U : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ)
    (ψ : Fin (2 ^ N) → ℂ) :
    sqNorm (Matrix.mulVec U ψ) = sqNorm ψ := by
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hC : (∑ s : Fin (2 ^ N),
      (starRingEnd ℂ ((Matrix.mulVec U ψ) s) * (Matrix.mulVec U ψ) s : ℂ))
      = ∑ t : Fin (2 ^ N), (starRingEnd ℂ (ψ t) * ψ t : ℂ) := by
    simp only [Matrix.mulVec_apply_eq_sum]
    simp only [map_sum (starRingEnd ℂ) _ Finset.univ]
    simp only [map_mul]
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have h_swap : ∀ y : Fin (2 ^ N),
        (∑ x : Fin (2 ^ N), ∑ j : Fin (2 ^ N),
          (starRingEnd ℂ) (U x y) * (starRingEnd ℂ) (ψ y) * (U x j * ψ j))
        = ∑ j : Fin (2 ^ N), ∑ x : Fin (2 ^ N),
          (starRingEnd ℂ) (U x y) * (starRingEnd ℂ) (ψ y) * (U x j * ψ j) :=
      fun y => Finset.sum_comm
    simp only [h_swap]
    have h_factor : ∀ x j : Fin (2 ^ N),
        (∑ s : Fin (2 ^ N),
          (starRingEnd ℂ) (U s x) * (starRingEnd ℂ) (ψ x) * (U s j * ψ j))
        = (∑ s : Fin (2 ^ N), (starRingEnd ℂ) (U s x) * U s j) *
          (starRingEnd ℂ) (ψ x) * ψ j := by
      intro x j
      have h_term : ∀ s : Fin (2 ^ N),
          (starRingEnd ℂ) (U s x) * (starRingEnd ℂ) (ψ x) * (U s j * ψ j)
          = ((starRingEnd ℂ) (U s x) * U s j) *
            ((starRingEnd ℂ) (ψ x) * ψ j) := fun s => by ring
      simp only [h_term, ← Finset.sum_mul, ← mul_assoc]
    simp only [h_factor]
    have h_gram : ∀ x j : Fin (2 ^ N),
        (∑ s : Fin (2 ^ N), (starRingEnd ℂ) (U s x) * U s j)
        = (star U * U) x j := by
      intro x j
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro s _
      rw [Matrix.star_apply, ← starRingEnd_apply]
    simp only [h_gram]
    have h_one : ∀ x j : Fin (2 ^ N), (star U * U) x j =
        (if x = j then (1 : ℂ) else 0) := by
      intro x j
      have h_eq : (star U * U) x j = (1 : Matrix _ _ ℂ) x j :=
        congrArg (fun M => M x j) hUU
      rw [h_eq, Matrix.one_apply]
    simp only [h_one]
    have h_inner : ∀ x : Fin (2 ^ N),
        (∑ j : Fin (2 ^ N),
          (if x = j then (1 : ℂ) else 0) * (starRingEnd ℂ) (ψ x) * ψ j)
        = (starRingEnd ℂ) (ψ x) * ψ x := by
      intro x
      have h_term : ∀ j : Fin (2 ^ N),
          (if x = j then (1 : ℂ) else 0) * (starRingEnd ℂ) (ψ x) * ψ j
          = if x = j then (starRingEnd ℂ) (ψ x) * ψ j else 0 := by
        intro j
        by_cases h : x = j
        · simp only [ite_eq_left h, one_mul]
        · simp only [ite_eq_right h, zero_mul]
      simp only [h_term]
      exact Fintype.sum_ite_eq x _
    simp only [h_inner]
  have hR := congrArg Complex.re hC
  simp only [Complex.re_sum] at hR
  unfold sqNorm
  exact hR

/-- A well-formed gate preserves the squared norm. -/
theorem sqNorm_applyGate {N : ℕ} {g : QGate} (hg : QGateWellFormed N g)
    (ψ : Fin (2 ^ N) → ℂ) :
    sqNorm (applyGate N g ψ) = sqNorm ψ := by
  rw [applyGate_eq_gateMatrix_mulVec hg]
  exact sqNorm_mulVec_unitary (gateMatrix_mem_unitaryGroup hg) ψ

/-- A circuit of well-formed gates preserves the squared norm. -/
theorem sqNorm_applyCircuit {N : ℕ} {gs : List QGate}
    (hgs : ∀ g ∈ gs, QGateWellFormed N g) (ψ : Fin (2 ^ N) → ℂ) :
    sqNorm (applyCircuit N gs ψ) = sqNorm ψ := by
  induction gs generalizing ψ with
  | nil => simp [applyCircuit]
  | cons hd tl ih =>
    have hg_hd : QGateWellFormed N hd := hgs hd List.mem_cons_self
    have hgs_tl : ∀ g ∈ tl, QGateWellFormed N g :=
      fun g hg => hgs g (List.mem_cons_of_mem hd hg)
    have hfold : applyCircuit N (hd :: tl) ψ =
        applyCircuit N tl (applyGate N hd ψ) := by
      simp [applyCircuit, List.foldl_cons]
    rw [hfold, ih hgs_tl, sqNorm_applyGate hg_hd]

/-- Applying concatenated circuits is applying the second after the first. -/
theorem applyCircuit_append (N : ℕ) (gs hs : List QGate)
    (ψ : Fin (2 ^ N) → ℂ) :
    applyCircuit N (gs ++ hs) ψ = applyCircuit N hs (applyCircuit N gs ψ) := by
  simp [applyCircuit, List.foldl_append]

/-- The squared norm of a tensor product is the product of squared norms. -/
theorem sqNorm_tensorProd {a b : ℕ} (φ : Fin (2 ^ a) → ℂ)
    (ψ : Fin (2 ^ b) → ℂ) :
    sqNorm (tensorProd φ ψ) = sqNorm φ * sqNorm ψ := by
  have hpow : 2 ^ (a + b) = 2 ^ b * 2 ^ a := by rw [pow_add, Nat.mul_comm]
  let e : Fin (2 ^ (a + b)) ≃ Fin (2 ^ a) × Fin (2 ^ b) :=
    (finCongr hpow).trans finProdFinEquiv.symm |>.trans (Equiv.prodComm _ _)
  have he1 : ∀ s : Fin (2 ^ (a + b)), (e s).1.val = s.val % 2 ^ a := by
    intro s
    simp only [e, Equiv.trans_apply, finCongr_apply, finProdFinEquiv_symm_apply,
      Equiv.prodComm_apply]
    show ((Fin.cast hpow s).modNat).val = _
    show (Fin.cast hpow s).val % 2 ^ a = _
    rw [Fin.val_cast]
  have he2 : ∀ s : Fin (2 ^ (a + b)), (e s).2.val = s.val / 2 ^ a := by
    intro s
    simp only [e, Equiv.trans_apply, finCongr_apply, finProdFinEquiv_symm_apply,
      Equiv.prodComm_apply]
    show ((Fin.cast hpow s).divNat).val = _
    show (Fin.cast hpow s).val / 2 ^ a = _
    rw [Fin.val_cast]
  unfold sqNorm tensorProd
  simp only [conj_mul_prod_re]
  have hfg : ∀ s : Fin (2 ^ (a + b)),
      (starRingEnd ℂ (φ ⟨s.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩) *
        φ ⟨s.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩).re *
        (starRingEnd ℂ (ψ ⟨s.val / 2 ^ a, by
          have h : s.val < 2 ^ b * 2 ^ a := by
            calc s.val < 2 ^ (a + b) := s.isLt
              _ = 2 ^ a * 2 ^ b := by rw [pow_add]
              _ = 2 ^ b * 2 ^ a := by rw [Nat.mul_comm]
          exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h⟩) *
        ψ ⟨s.val / 2 ^ a, by
          have h : s.val < 2 ^ b * 2 ^ a := by
            calc s.val < 2 ^ (a + b) := s.isLt
              _ = 2 ^ a * 2 ^ b := by rw [pow_add]
              _ = 2 ^ b * 2 ^ a := by rw [Nat.mul_comm]
          exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h⟩).re =
      (fun p : Fin (2 ^ a) × Fin (2 ^ b) =>
        (starRingEnd ℂ (φ p.1) * φ p.1).re *
        (starRingEnd ℂ (ψ p.2) * ψ p.2).re) (e s) := by
    intro s
    have h1 : (⟨s.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ a)) =
        (e s).1 := Fin.ext (by rw [he1])
    have h2 : (⟨s.val / 2 ^ a, by
          have h : s.val < 2 ^ b * 2 ^ a := by
            calc s.val < 2 ^ (a + b) := s.isLt
              _ = 2 ^ a * 2 ^ b := by rw [pow_add]
              _ = 2 ^ b * 2 ^ a := by rw [Nat.mul_comm]
          exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h⟩ : Fin (2 ^ b)) =
        (e s).2 := Fin.ext (by rw [he2])
    rw [h1, h2]
  rw [Fintype.sum_equiv e _
    (fun p : Fin (2 ^ a) × Fin (2 ^ b) =>
      (starRingEnd ℂ (φ p.1) * φ p.1).re *
      (starRingEnd ℂ (ψ p.2) * ψ p.2).re) hfg]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- A computational-basis state is a unit vector. -/
theorem sqNorm_basisState (x : List Bool) : sqNorm (basisState x) = 1 := by
  have hq : qNumOf x < 2 ^ x.length := qNumOf_lt_pow x
  unfold sqNorm basisState
  have hterm : ∀ s : Fin (2 ^ x.length),
      (starRingEnd ℂ (if s.val = qNumOf x then (1 : ℂ) else 0) *
        (if s.val = qNumOf x then (1 : ℂ) else 0)).re =
      if s = ⟨qNumOf x, hq⟩ then (1 : ℝ) else 0 := by
    intro s
    by_cases h : s.val = qNumOf x
    · have hs : s = ⟨qNumOf x, hq⟩ := Fin.ext h
      simp only [ite_eq_left h, ite_eq_left hs]
      rw [conj_mul_self_re_eq_normSq, Complex.normSq_one]
    · have hs : s ≠ ⟨qNumOf x, hq⟩ := fun contra => h (congrArg Fin.val contra)
      simp only [ite_eq_right h, ite_eq_right hs]
      rw [conj_mul_self_re_eq_normSq, Complex.normSq_zero]
  simp only [hterm]
  exact Fintype.sum_ite_eq' _ _

/-- The all-zero state is a unit vector. -/
theorem sqNorm_zeroState (a : ℕ) : sqNorm (zeroState a) = 1 := by
  have h0 : 0 < 2 ^ a := by positivity
  unfold sqNorm zeroState
  have hterm : ∀ s : Fin (2 ^ a),
      (starRingEnd ℂ (if s.val = 0 then (1 : ℂ) else 0) *
        (if s.val = 0 then (1 : ℂ) else 0)).re =
      if s = ⟨0, h0⟩ then (1 : ℝ) else 0 := by
    intro s
    by_cases h : s.val = 0
    · have hs : s = ⟨0, h0⟩ := Fin.ext h
      simp only [ite_eq_left h, ite_eq_left hs]
      rw [conj_mul_self_re_eq_normSq, Complex.normSq_one]
    · have hs : s ≠ ⟨0, h0⟩ := fun contra => h (congrArg Fin.val contra)
      simp only [ite_eq_right h, ite_eq_right hs]
      rw [conj_mul_self_re_eq_normSq, Complex.normSq_zero]
  simp only [hterm]
  exact Fintype.sum_ite_eq' _ _

/-- The BQP initial state is a unit vector. -/
theorem sqNorm_bqpInitState (x : List Bool) (a : ℕ) :
    sqNorm (bqpInitState x a) = 1 := by
  unfold bqpInitState
  rw [sqNorm_tensorProd, sqNorm_basisState, sqNorm_zeroState, mul_one]

/-- The squared norm is nonnegative. -/
theorem sqNorm_nonneg {m : ℕ} (ψ : Fin (2 ^ m) → ℂ) : 0 ≤ sqNorm ψ := by
  unfold sqNorm
  apply Finset.sum_nonneg
  intro s _
  exact conj_mul_self_re_nonneg (ψ s)

/-- Acceptance probability is nonnegative. -/
theorem acceptProb_nonneg {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) :
    0 ≤ acceptProb ψ := by
  unfold acceptProb
  apply Finset.sum_nonneg
  intro s _
  by_cases h : qBit 0 s.val = 1
  · simp only [h]
    exact conj_mul_self_re_nonneg (ψ s)
  · simp [h]

/-- Acceptance probability plus the complementary outcome probability is the
squared norm. -/
theorem acceptProb_add_compl {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) :
    acceptProb ψ +
        (∑ s : Fin (2 ^ N), if qBit 0 s.val = 1 then 0
          else (starRingEnd ℂ (ψ s) * ψ s).re) = sqNorm ψ := by
  unfold acceptProb sqNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : qBit 0 s.val = 1 <;> simp [h, add_comm]

/-- For a unit vector, acceptance probability is at most `1`. -/
theorem acceptProb_le_one {N : ℕ} {ψ : Fin (2 ^ N) → ℂ}
    (hψ : sqNorm ψ = 1) : acceptProb ψ ≤ 1 := by
  have h := acceptProb_add_compl ψ
  rw [hψ] at h
  have hnonneg : 0 ≤ (∑ s : Fin (2 ^ N), if qBit 0 s.val = 1 then (0 : ℝ)
      else (starRingEnd ℂ (ψ s) * ψ s).re) := by
    apply Finset.sum_nonneg
    intro s _
    by_cases hb : qBit 0 s.val = 1
    · simp [hb]
    · simp only [hb]
      exact conj_mul_self_re_nonneg (ψ s)
  linarith

end Cslib.Complexity.Classes
