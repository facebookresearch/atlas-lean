/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PauliBasisChange
public import CSLibExt.Computability.Complexity.QuantumGates.GateAction
public import MathlibExt.Quantum.PauliExpansion
import CSLibExt.Computability.Complexity.QMA.BlockEigenbasis
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

/-!
# Per-label measurement circuits

For one Pauli label `(a, b)` addressed at injective positions `addr`, all
below `N`, and an ancilla `0 < anc < N` outside them, a
circuit of per-qubit basis changes (`ωH`, and `S†` then `ωH` for `Y`
letters), parity accumulation of the changed bits into a clean ancilla by
CNOTs, an optional sign flip, and a swap of the answer into qubit `0`
measures the embedded Pauli string: its acceptance weight `acceptProb` on
any state supported on a clean ancilla is
`(sqNorm ψ - σ * ⟨ψ|P_emb|ψ⟩) / 2` for `σ = ±1`, which is the acceptance
probability when `sqNorm ψ = 1`. The embedding
`embedLocal` of a `k`-qubit operator at addressed qubits is defined here.
It is the `k`-qubit form of the `gateMatrix` agreement convention that
the two-local-term embedding `embedTerm` of the local-Hamiltonian
development also follows.

Source: A. Yu. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and
Quantum Computation, American Mathematical Society, 2002, Chapter 14
(local Hamiltonian terms measured through basis changes and parity).

The acceptance identity proved here is the per-label Pauli test; the
matching test-acceptance form appears in Morimae, Nagaj, and Schuch,
arXiv:1510.06789, Section IV.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QMA

set_option autoImplicit false

open scoped Matrix BigOperators
open Cslib.Complexity.Classes Cslib.Complexity.Classes.QuantumGates
open MathlibExt.Quantum.PauliExpansion

/-! ## Embedding of local operators -/

/-- Bits of basis index `s` at the addressed qubits, as `ZMod 2` values. -/
def localBits {k : ℕ} (addr : Fin k → ℕ) (s : ℕ) : Fin k → ZMod 2 :=
  fun i => ((qBit (addr i) s).val : ZMod 2)

open Classical in
/-- A `2^k × 2^k` operator on the addressed qubits, tensored with the
identity elsewhere when `addr` is injective with values below `N` (the
`gateMatrix` agreement convention, generalized to `k` qubits). -/
noncomputable def embedLocal (N : ℕ) {k : ℕ} (addr : Fin k → ℕ)
    (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  fun s t =>
    if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val) then
      A (localBits addr s.val) (localBits addr t.val)
    else 0

/-- Embedding preserves addition. -/
theorem embedLocal_add (N : ℕ) {k : ℕ} (addr : Fin k → ℕ)
    (A B : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) :
    embedLocal N addr (A + B) = embedLocal N addr A + embedLocal N addr B := by
  ext s t
  by_cases h : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
  · simp only [embedLocal, Matrix.add_apply, ite_eq_left h]
  · simp only [embedLocal, Matrix.add_apply, ite_eq_right h, add_zero]

/-- Embedding preserves scalar multiplication. -/
theorem embedLocal_smul (N : ℕ) {k : ℕ} (addr : Fin k → ℕ) (c : ℂ)
    (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) :
    embedLocal N addr (c • A) = c • embedLocal N addr A := by
  ext s t
  by_cases h : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
  · simp only [embedLocal, Matrix.smul_apply, ite_eq_left h]
  · simp only [embedLocal, Matrix.smul_apply, ite_eq_right h, smul_zero]

/-- The embedding as a linear map. -/
noncomputable def embedLocalLinearMap (N : ℕ) {k : ℕ} (addr : Fin k → ℕ) :
    Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ →ₗ[ℂ]
      Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  { toFun := embedLocal N addr, map_add' := embedLocal_add N addr,
    map_smul' := embedLocal_smul N addr }

/-- The embedded Pauli string `P_emb` of a label. -/
noncomputable def pauliEmb (N : ℕ) {k : ℕ} (addr : Fin k → ℕ) (a b : Fin k → ZMod 2) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  embedLocal N addr (hermPauli a b)

/-- The quadratic form `⟨ψ|P_emb|ψ⟩`, real since `P_emb` is Hermitian: the
expectation of `P_emb` when `sqNorm ψ = 1`. -/
noncomputable def pauliExpect {N k : ℕ} (addr : Fin k → ℕ) (a b : Fin k → ZMod 2)
    (ψ : Fin (2 ^ N) → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (pauliEmb N addr a b *ᵥ ψ)).re

private theorem agree_symm {k : ℕ} (addr : Fin k → ℕ) (s t : ℕ)
    (h : ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s = qBit q t) :
    ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q t = qBit q s :=
  fun q hq => (h q hq).symm

private theorem agree_trans {k : ℕ} (addr : Fin k → ℕ) (s u t : ℕ)
    (h1 : ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s = qBit q u)
    (h2 : ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q u = qBit q t) :
    ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s = qBit q t :=
  fun q hq => (h1 q hq).trans (h2 q hq)

private theorem agree_refl {k : ℕ} (addr : Fin k → ℕ) (s : ℕ) :
    ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s = qBit q s :=
  fun _ _ => rfl

private theorem eq_of_agree {N k : ℕ} {addr : Fin k → ℕ} {s t : Fin (2 ^ N)}
    (h : ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
    (hloc : localBits addr s.val = localBits addr t.val) : s = t := by
  apply fin_eq_of_qBit_eq
  intro kk hkk
  by_cases hex : ∃ i, addr i = kk
  · obtain ⟨i, rfl⟩ := hex
    have hi := congrFun hloc i
    simp only [localBits] at hi
    have h1 := Fin.isLt (qBit (addr i) s.val)
    have h2 := Fin.isLt (qBit (addr i) t.val)
    have hval : (qBit (addr i) s.val).val = (qBit (addr i) t.val).val := by
      have hcongr := congrArg ZMod.val hi
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hcongr
    exact Fin.eq_of_val_eq hval
  · have hne : ∀ i, addr i ≠ kk := fun i hi => hex ⟨i, hi⟩
    exact h kk hne

private theorem pauliXZ_zero_zero {k : ℕ} :
    MathlibExt.Quantum.PauliXZ.pauliXZ (0 : Fin k → ZMod 2)
      (0 : Fin k → ZMod 2) = 1 := by
  ext x y
  rw [MathlibExt.Quantum.PauliXZ.pauliXZ_apply, add_zero]
  simp only [zero_dotProduct]
  rw [ZMod.val_zero, pow_zero]
  by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]

private theorem hermPauli_zero_zero {k : ℕ} :
    hermPauli (0 : Fin k → ZMod 2) (0 : Fin k → ZMod 2) = 1 := by
  unfold hermPauli
  have hexp :
      (∑ i, ((0 : Fin k → ZMod 2) i).val * ((0 : Fin k → ZMod 2) i).val) = 0 := by
    simp
  rw [hexp, pow_zero, one_smul]
  exact pauliXZ_zero_zero

private def zmodToFinTwo (z : ZMod 2) : Fin 2 := ⟨z.val, ZMod.val_lt z⟩

private theorem zmodToFinTwo_val (z : ZMod 2) : (zmodToFinTwo z).val = z.val := rfl

private theorem fold_qBit_off {N k : ℕ} (addr : Fin k → ℕ)
    (x : Fin k → ZMod 2) (l : List (Fin k)) (u : Fin (2 ^ N)) (q : ℕ)
    (hq : ∀ i ∈ l, addr i ≠ q) :
    qBit q (l.foldl (fun u i => setQBit N (addr i) (zmodToFinTwo (x i)) u) u).val =
      qBit q u.val := by
  revert hq u
  induction l with
  | nil =>
    intro u hq
    rw [List.foldl_nil]
  | cons i l' ih =>
    intro u hq
    rw [List.foldl_cons]
    have hq' : ∀ i' ∈ l', addr i' ≠ q :=
      fun i' hi' => hq i' (List.mem_cons.mpr (Or.inr hi'))
    rw [ih _ hq']
    exact qBit_setQBit_of_ne (Ne.symm (hq i (List.mem_cons.mpr (Or.inl rfl)))) _ _

private theorem fold_qBit_mem {N k : ℕ} (addr : Fin k → ℕ)
    (x : Fin k → ZMod 2) (l : List (Fin k)) (u : Fin (2 ^ N)) (j : Fin k)
    (hj : j ∈ l) (hnodup : l.Nodup)
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N) :
    qBit (addr j) (l.foldl (fun u i => setQBit N (addr i) (zmodToFinTwo (x i)) u) u).val =
      zmodToFinTwo (x j) := by
  revert hj hnodup u
  induction l with
  | nil =>
    intro u hj hnodup
    simp at hj
  | cons i l' ih =>
    intro u hj hnodup
    rw [List.foldl_cons]
    rw [List.mem_cons] at hj
    rw [List.nodup_cons] at hnodup
    obtain ⟨hni, hnodup'⟩ := hnodup
    cases hj with
    | inl hji =>
      rw [hji]
      have hpres : ∀ i' ∈ l', addr i' ≠ addr i :=
        fun i' hi' heq => hni (haddr heq ▸ hi')
      rw [fold_qBit_off addr x l' _ _ hpres]
      exact qBit_setQBit_self (hlt i) _ _
    | inr hj' =>
      exact ih _ hj' hnodup'

private noncomputable def fiberIndex {N k : ℕ} (addr : Fin k → ℕ) (s : Fin (2 ^ N))
    (x : Fin k → ZMod 2) : Fin (2 ^ N) :=
  (List.finRange k).foldl (fun u i => setQBit N (addr i) (zmodToFinTwo (x i)) u) s

private theorem fiberIndex_localBits {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (s : Fin (2 ^ N)) (x : Fin k → ZMod 2) :
    localBits addr (fiberIndex addr s x).val = x := by
  funext j
  simp only [localBits, fiberIndex]
  rw [fold_qBit_mem addr x _ _ j (List.mem_finRange j) (List.nodup_finRange k)
    haddr hlt, zmodToFinTwo_val]
  exact ZMod.natCast_zmod_val (x j)

private theorem fiberIndex_agree {N k : ℕ} (addr : Fin k → ℕ)
    (s : Fin (2 ^ N)) (x : Fin k → ZMod 2) :
    ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q (fiberIndex addr s x).val := by
  intro q hq
  simp only [fiberIndex]
  exact (fold_qBit_off addr x _ s q (fun i _ => hq i)).symm

private theorem fiberIndex_injective {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N) (s : Fin (2 ^ N)) :
    Function.Injective (fiberIndex addr s) := by
  intro x y hxy
  have hx := fiberIndex_localBits haddr hlt s x
  have hy := fiberIndex_localBits haddr hlt s y
  rw [hxy] at hx
  exact hx.symm.trans hy

private theorem fiberIndex_cover {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (s : Fin (2 ^ N)) (u : Fin (2 ^ N))
    (h : ∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val) :
    u = fiberIndex addr s (localBits addr u.val) := by
  apply fin_eq_of_qBit_eq
  intro kk hkk
  by_cases hex : ∃ i, addr i = kk
  · obtain ⟨i, rfl⟩ := hex
    simp only [fiberIndex]
    have hmem := fold_qBit_mem addr (localBits addr u.val) (List.finRange k) s i
      (List.mem_finRange i) (List.nodup_finRange k) haddr hlt
    rw [hmem]
    have hval : (zmodToFinTwo (localBits addr u.val i)).val
        = (qBit (addr i) u.val).val := by
      rw [zmodToFinTwo_val]
      simp only [localBits]
      rw [ZMod.val_natCast_of_lt (Fin.isLt _)]
    exact Fin.eq_of_val_eq hval.symm
  · have hne : ∀ i, addr i ≠ kk := fun i hi => hex ⟨i, hi⟩
    have h1 := h kk hne
    have h2 := fiberIndex_agree addr s (localBits addr u.val) kk hne
    exact h1.symm.trans h2

open Classical in
private theorem pauliEmb_mul_self {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (a b : Fin k → ZMod 2) :
    pauliEmb N addr a b * pauliEmb N addr a b = 1 := by
  ext s t
  rw [Matrix.mul_apply]
  simp only [pauliEmb, embedLocal]
  by_cases hC : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
  · set F : Fin (2 ^ N) → ℂ := fun u =>
      (if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
        then hermPauli a b (localBits addr s.val) (localBits addr u.val) else 0) *
      (if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q u.val = qBit q t.val)
        then hermPauli a b (localBits addr u.val) (localBits addr t.val) else 0) with hF
    have hvan : ∀ u ∈ (Finset.univ : Finset (Fin (2 ^ N))),
        u ∉ Finset.image (fiberIndex addr s) Finset.univ → F u = 0 := by
      intro u _ hu
      by_cases h1 : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
      · exfalso
        apply hu
        rw [Finset.mem_image]
        exact ⟨localBits addr u.val, Finset.mem_univ _,
          (fiberIndex_cover haddr hlt s u h1).symm⟩
      · simp only [hF]
        rw [ite_eq_right h1, zero_mul]
    have hsub : ∑ u ∈ Finset.image (fiberIndex addr s) Finset.univ, F u
        = ∑ u ∈ Finset.univ, F u :=
      Finset.sum_subset (Finset.subset_univ _) hvan
    rw [← hsub]
    have hinj : Set.InjOn (fiberIndex addr s)
        ↑(Finset.univ : Finset (Fin k → ZMod 2)) :=
      fun x _ y _ hxy => fiberIndex_injective haddr hlt s hxy
    rw [Finset.sum_image hinj]
    have hfib : ∀ x : Fin k → ZMod 2, F (fiberIndex addr s x)
        = hermPauli a b (localBits addr s.val) x
          * hermPauli a b x (localBits addr t.val) := by
      intro x
      have h1 := fiberIndex_agree addr s x
      have h2 : (∀ q : ℕ, (∀ i, addr i ≠ q)
          → qBit q (fiberIndex addr s x).val = qBit q t.val) :=
        agree_trans addr _ _ _ (agree_symm addr s.val _ h1) hC
      have hLx : localBits addr (fiberIndex addr s x).val = x :=
        fiberIndex_localBits haddr hlt s x
      simp only [hF]
      rw [ite_eq_left h1, ite_eq_left h2, hLx]
    simp only [hfib]
    have hHH := hermPauli_mul_self a b
    have hmul : (∑ x, hermPauli a b (localBits addr s.val) x
          * hermPauli a b x (localBits addr t.val))
        = (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ)
          (localBits addr s.val) (localBits addr t.val) := by
      rw [← Matrix.mul_apply, hHH]
    rw [hmul, Matrix.one_apply, Matrix.one_apply]
    by_cases hst : s = t
    · subst hst
      simp
    · have hLne : localBits addr s.val ≠ localBits addr t.val :=
        fun heq => hst (eq_of_agree hC heq)
      rw [ite_eq_right hLne, ite_eq_right hst]
  · have hst : s ≠ t := by
      rintro rfl
      exact hC (agree_refl addr _)
    rw [Matrix.one_apply, ite_eq_right hst]
    have hterm : ∀ u : Fin (2 ^ N),
        (if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
          then hermPauli a b (localBits addr s.val) (localBits addr u.val) else 0) *
        (if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q u.val = qBit q t.val)
          then hermPauli a b (localBits addr u.val) (localBits addr t.val) else 0) = 0 := by
      intro u
      by_cases h1 : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
      · by_cases h2 : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q u.val = qBit q t.val)
        · exfalso
          exact hC (agree_trans addr s.val u.val t.val h1 h2)
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    conv_rhs => rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin (2 ^ N))))]
    exact Finset.sum_congr rfl (fun u _ => hterm u)

private theorem sqNorm_mulVec_unitary {N : ℕ}
    {U : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (hU : star U * U = 1) (ψ : Fin (2 ^ N) → ℂ) :
    sqNorm (U *ᵥ ψ) = sqNorm ψ := by
  rw [sqNorm_eq_re_star_dotProduct, sqNorm_eq_re_star_dotProduct]
  have hdot : star (U *ᵥ ψ) ⬝ᵥ (U *ᵥ ψ) = star ψ ⬝ᵥ ψ := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [hdot]

private theorem star_dotProduct_re_symm {N : ℕ} (φ ψ : Fin (2 ^ N) → ℂ) :
    (star φ ⬝ᵥ ψ).re = (star ψ ⬝ᵥ φ).re := by
  rw [Matrix.star_dotProduct, ← starRingEnd_apply, Complex.conj_re]

private theorem sqNorm_add {N : ℕ} (ψ φ : Fin (2 ^ N) → ℂ) :
    sqNorm (ψ + φ)
      = sqNorm ψ + sqNorm φ + ((star ψ ⬝ᵥ φ).re + (star ψ ⬝ᵥ φ).re) := by
  rw [sqNorm_eq_re_star_dotProduct, star_add, add_dotProduct, dotProduct_add, dotProduct_add,
    Complex.add_re, Complex.add_re, Complex.add_re,
    ← sqNorm_eq_re_star_dotProduct ψ, ← sqNorm_eq_re_star_dotProduct φ,
    star_dotProduct_re_symm φ ψ]
  ring

private theorem sqNorm_sub {N : ℕ} (ψ φ : Fin (2 ^ N) → ℂ) :
    sqNorm (ψ - φ)
      = sqNorm ψ + sqNorm φ - ((star ψ ⬝ᵥ φ).re + (star ψ ⬝ᵥ φ).re) := by
  rw [sqNorm_eq_re_star_dotProduct, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    Complex.sub_re, Complex.sub_re, Complex.sub_re,
    ← sqNorm_eq_re_star_dotProduct ψ, ← sqNorm_eq_re_star_dotProduct φ,
    star_dotProduct_re_symm φ ψ]
  ring

/-- The embedded Pauli string is Hermitian. -/
theorem pauliEmb_isHermitian {N k : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) :
    (pauliEmb N addr a b).IsHermitian := by
  have hH := hermPauli_isHermitian a b
  unfold Matrix.IsHermitian
  ext s t
  rw [Matrix.conjTranspose_apply]
  simp only [pauliEmb, embedLocal]
  by_cases h : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
  · rw [ite_eq_left h, ite_eq_left (agree_symm addr s.val t.val h)]
    have hentry :=
      congrFun (congrFun hH.eq (localBits addr s.val)) (localBits addr t.val)
    rw [Matrix.conjTranspose_apply] at hentry
    exact hentry
  · rw [ite_eq_right h,
      ite_eq_right (fun h' => h (agree_symm addr t.val s.val h'))]
    simp

/-- The identity label embeds to the identity. -/
theorem pauliEmb_zero_zero {N k : ℕ} {addr : Fin k → ℕ} :
    pauliEmb N addr 0 0 = 1 := by
  have hH00 : hermPauli (0 : Fin k → ZMod 2) 0 = 1 := hermPauli_zero_zero
  unfold pauliEmb
  rw [hH00]
  ext s t
  simp only [embedLocal]
  by_cases hst : s = t
  · subst hst
    rw [ite_eq_left (agree_refl addr _)]
    simp only [Matrix.one_apply]
  · by_cases h : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q t.val)
    · rw [ite_eq_left h, Matrix.one_apply, Matrix.one_apply, ite_eq_right hst,
        ite_eq_right (fun heq => hst (eq_of_agree h heq))]
    · rw [ite_eq_right h, Matrix.one_apply, ite_eq_right hst]

/-- The Pauli quadratic form is bounded by the squared norm: for injective
addresses `addr` with every `addr i < N`, `|⟨ψ|P_emb|ψ⟩| ≤ sqNorm ψ`. -/
theorem abs_pauliExpect_le {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (a b : Fin k → ZMod 2) (ψ : Fin (2 ^ N) → ℂ) :
    |pauliExpect addr a b ψ| ≤ sqNorm ψ := by
  have hH : (pauliEmb N addr a b).IsHermitian := pauliEmb_isHermitian a b
  have hsq := pauliEmb_mul_self haddr hlt a b
  have hstar : star (pauliEmb N addr a b) * pauliEmb N addr a b = 1 := by
    rw [Matrix.star_eq_conjTranspose, hH.eq, hsq]
  have hnorm := sqNorm_mulVec_unitary hstar ψ
  have hplus := sqNorm_add ψ (pauliEmb N addr a b *ᵥ ψ)
  have hminus := sqNorm_sub ψ (pauliEmb N addr a b *ᵥ ψ)
  have hn1 := sqNorm_nonneg (ψ + pauliEmb N addr a b *ᵥ ψ)
  have hn2 := sqNorm_nonneg (ψ - pauliEmb N addr a b *ᵥ ψ)
  unfold pauliExpect
  rw [abs_le]
  constructor <;> linarith [hnorm, hplus, hminus, hn1, hn2]

/-! ## The per-label circuit -/

/-- Basis change for the letter `(a, b)` on qubit `q` with spectator `p`,
in circuit order: `I`/`Z` letters need none, `X` needs `ωH`, `Y` needs
`S†` then `ωH`. -/
def basisChangeGates (a b : ZMod 2) (q p : ℕ) : List QGate :=
  if a = 1 then
    (if b = 1 then [embeddedGate sDagGate q p, embeddedGate omegaH q p]
     else [embeddedGate omegaH q p])
  else []

/-- Parity contribution of a non-identity letter: CNOT from its qubit into
the answer ancilla. -/
def parityGates (a b : ZMod 2) (q anc : ℕ) : List QGate :=
  if a = 0 ∧ b = 0 then [] else [controlledGate xGate q anc]

/-- The per-label core: per-qubit basis changes and parity into `anc`,
then `X` on `anc` iff the sign is negative. The ancilla is the spectator
of every basis-change gate; the sign gate acts on the ancilla with qubit
`0` as spectator. -/
def perLabelCore {k : ℕ} (addr : Fin k → ℕ) (a b : Fin k → ZMod 2) (neg : Bool)
    (anc : ℕ) : List QGate :=
  (List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc) ++
    (if neg then [embeddedGate xGate anc 0] else [])

/-- The output move: swap qubit `0` with the answer ancilla. -/
def outputSwap (anc : ℕ) : QGate := (0, anc, swapEntries)

/-- The per-label measurement circuit: the core, then the output move. -/
def perLabelCircuit {k : ℕ} (addr : Fin k → ℕ) (a b : Fin k → ZMod 2) (neg : Bool)
    (anc : ℕ) : List QGate :=
  perLabelCore addr a b neg anc ++ [outputSwap anc]

private theorem flatMap_length_le_of_le {α β : Type} (f : α → List β)
    (l : List α) (n : ℕ) (h : ∀ x ∈ l, (f x).length ≤ n) :
    (l.flatMap f).length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx : (f x).length ≤ n := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, (f y).length ≤ n :=
      fun y hy => h y (List.mem_cons_of_mem x hy)
    have ih' := ih hxs
    have hmul : n * (xs.length + 1) = n * xs.length + n := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Every gate of the per-label circuit is well-formed when every address
`addr i` is below `N`, the ancilla satisfies `0 < anc < N`, and no address
equals the ancilla. The addresses need not be injective. -/
theorem perLabelCircuit_wellFormed {N k anc : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) (neg : Bool)
    (hlt : ∀ i, addr i < N) (hanc0 : 0 < anc) (hanc : anc < N)
    (hne : ∀ i, addr i ≠ anc) :
    ∀ g ∈ perLabelCircuit addr a b neg anc, QGateWellFormed N g := by
  intro g hg
  unfold perLabelCircuit perLabelCore at hg
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hg
  rcases hg with (⟨i, _, hg⟩ | hg_sign) | rfl
  · rcases hg with hg_basis | hg_parity
    · unfold basisChangeGates at hg_basis
      by_cases ha : a i = 1
      · simp only [ha, ite_true] at hg_basis
        by_cases hbb : b i = 1
        · simp only [hbb, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hg_basis
          rcases hg_basis with rfl | rfl
          · exact embeddedGate_wellFormed _ sDagGate_unitary (hne i) (hlt i) hanc
          · exact embeddedGate_wellFormed _ omegaH_unitary (hne i) (hlt i) hanc
        · simp only [hbb, ite_false, List.mem_singleton] at hg_basis
          rcases hg_basis with rfl
          exact embeddedGate_wellFormed _ omegaH_unitary (hne i) (hlt i) hanc
      · simp [ha] at hg_basis
    · unfold parityGates at hg_parity
      by_cases h : a i = 0 ∧ b i = 0
      · simp [h] at hg_parity
      · simp only [h, ite_false, List.mem_singleton] at hg_parity
        rcases hg_parity with rfl
        exact controlledGate_wellFormed _ xGate_unitary (hne i) (hlt i) hanc
  · by_cases hn : neg = true
    · simp only [hn, ite_true, List.mem_singleton] at hg_sign
      rcases hg_sign with rfl
      have hne0 : anc ≠ 0 := by omega
      have h0N : 0 < N := by omega
      exact embeddedGate_wellFormed _ xGate_unitary hne0 hanc h0N
    · simp [hn] at hg_sign
  · unfold outputSwap
    exact qGateWellFormed_swap hanc0 hanc
/-- The per-label circuit has at most `3k + 2` gates. -/
theorem perLabelCircuit_length_le {k anc : ℕ} (addr : Fin k → ℕ)
    (a b : Fin k → ZMod 2) (neg : Bool) :
    (perLabelCircuit addr a b neg anc).length ≤ 3 * k + 2 := by
  unfold perLabelCircuit perLabelCore
  rw [List.length_append, List.length_append]
  simp only [List.length_singleton]
  have h_per : ∀ i : Fin k,
      (basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc).length ≤ 3 := by
    intro i
    have hb : (basisChangeGates (a i) (b i) (addr i) anc).length ≤ 2 := by
      unfold basisChangeGates
      by_cases ha : a i = 1
      · simp only [ha, ite_true]
        by_cases hbb : b i = 1 <;> simp [hbb]
      · simp [ha]
    have hp : (parityGates (a i) (b i) (addr i) anc).length ≤ 1 := by
      unfold parityGates
      by_cases h : a i = 0 ∧ b i = 0 <;> simp [h]
    rw [List.length_append]
    omega
  have h1 : ((List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc)).length ≤ 3 * k := by
    have h := flatMap_length_le_of_le
      (fun i : Fin k => basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc) (List.finRange k) 3
      (fun x _ => h_per x)
    rwa [List.length_finRange] at h
  have h2 : (if neg then [embeddedGate xGate anc 0] else []).length ≤ 1 := by
    by_cases hn : neg = true <;> simp [hn]
  omega

/-- After the output swap with an ancilla `0 < anc < N`, acceptance reads
the ancilla bit of the pre-swap state. -/
theorem acceptProb_outputSwap {N anc : ℕ} (hanc0 : 0 < anc) (hanc : anc < N)
    (φ : Fin (2 ^ N) → ℂ) :
    acceptProb (applyCircuit N [outputSwap anc] φ) =
      ∑ s : Fin (2 ^ N),
        if qBit anc s.val = 1 then (starRingEnd ℂ (φ s) * φ s).re else 0 := by
  have h0N : 0 < N := Nat.lt_trans hanc0 hanc
  have hne2 : anc ≠ 0 := by omega
  unfold acceptProb outputSwap
  simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
  set e : Fin (2 ^ N) → Fin (2 ^ N) :=
    fun s => setQBit N 0 (qBit anc s.val) (setQBit N anc (qBit 0 s.val) s) with he
  have hswap : ∀ s : Fin (2 ^ N),
      applyGate N (0, anc, swapEntries) φ s = φ (e s) := by
    intro s
    simp only [he]
    apply applyGate_swap <;> assumption
  simp only [hswap]
  have hinv : Function.Involutive e := by
    intro s
    apply fin_eq_of_qBit_eq
    intro k _
    by_cases h0 : k = 0
    · subst h0
      simp [he, qBit_setQBit_self, qBit_setQBit_of_ne, h0N, hanc, hne2]
    · by_cases ha : k = anc
      · subst ha
        simp [he, qBit_setQBit_self, qBit_setQBit_of_ne, h0N, hanc, hne2]
      · simp [he, qBit_setQBit_of_ne, h0, ha]
  have hbij : Function.Bijective e := hinv.bijective
  have hq : ∀ s : Fin (2 ^ N), qBit anc (e s).val = qBit 0 s.val := by
    intro s
    simp [he, qBit_setQBit_self, qBit_setQBit_of_ne, hanc, hne2]
  apply Fintype.sum_bijective e hbij
    (fun s => if qBit 0 s.val = 1 then (starRingEnd ℂ (φ (e s)) * φ (e s)).re else 0)
    (fun s => if qBit anc s.val = 1 then (starRingEnd ℂ (φ s) * φ s).re else 0)
  intro s
  simp only [hq s]

/-! ## Core identity helpers -/

/-- One-qubit operator action at qubit `q`, in fiber form. -/
private def qAct (N q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin (2 ^ N) → ℂ) :
    Fin (2 ^ N) → ℂ :=
  fun s => ∑ d : Fin 2, A (qBit q s.val) d * φ (setQBit N q d s)

/-- The diagonal `Z` action at qubit `anc`. -/
private def zAnc (N anc : ℕ) (φ : Fin (2 ^ N) → ℂ) : Fin (2 ^ N) → ℂ :=
  fun s => (if qBit anc s.val = 1 then (-1 : ℂ) else 1) * φ s

/-- The one-letter Pauli matrices `1, Z, X, Y`. -/
private def letterMat (α β : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if α = 0 then (if β = 0 then 1 else !![1, 0; 0, -1])
  else (if β = 0 then !![0, 1; 1, 0] else !![0, -Complex.I; Complex.I, 0])

/-- The correlation `⟨φ| Z_anc P_emb |φ⟩` tracked through the core. -/
private noncomputable def ancCorr {N k : ℕ} (anc : ℕ) (addr : Fin k → ℕ) (a b : Fin k → ZMod 2)
    (φ : Fin (2 ^ N) → ℂ) : ℂ :=
  star φ ⬝ᵥ zAnc N anc (pauliEmb N addr a b *ᵥ φ)

/-- Every `Fin 2` bit is `0` or `1`. -/
private theorem fin2_dichot : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide

/-- Every `ZMod 2` element is `0` or `1`. -/
private theorem zmod2_dichot : ∀ γ : ZMod 2, γ = 0 ∨ γ = 1 := by decide

private theorem zmod2_val_one : (1 : ZMod 2).val = 1 := by decide
private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- A `Fin 2` value round-trips through `ZMod 2`. -/
private theorem fin2_cast_val (b : Fin 2) :
    (((b.val : ℕ) : ZMod 2).val) = b.val := by
  rcases fin2_dichot b with rfl | rfl <;> decide

/-- `(-1)`-powers multiply over `ZMod 2` sums. -/
private theorem neg_one_pow_val_add (u v : ZMod 2) :
    (-1 : ℂ) ^ ((u + v).val) = (-1 : ℂ) ^ (u.val) * (-1 : ℂ) ^ (v.val) := by
  rcases zmod2_dichot u with rfl | rfl <;> rcases zmod2_dichot v with rfl | rfl
  · simp
  · simp [zmod2_val_one]
  · simp [zmod2_val_one]
  · simp [zmod2_val_one, zmod2_one_add_one]

private theorem pauliComm_qBitCast_inj :
    Function.Injective (fun d : Fin 2 => (d.val : ZMod 2)) := by
  decide

/-- Entries of the one-letter Pauli matrices. -/
private theorem letterMat_apply (α β : ZMod 2) (y x : Fin 2) :
    letterMat α β y x =
      if (y.val : ZMod 2) = (x.val : ZMod 2) + α then
        Complex.I ^ (α.val * β.val) * (-1 : ℂ) ^ (β * (x.val : ZMod 2)).val
      else 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have v0 : (0 : ZMod 2).val = 0 := by decide
  rcases zmod2_dichot α with rfl | rfl <;> rcases zmod2_dichot β with rfl | rfl <;>
    fin_cases x <;> fin_cases y <;>
    simp [letterMat, h10, h01, zmod2_one_add_one, v0, zmod2_val_one]

/-- Reading the addressed bits after setting one addressed qubit. -/
private theorem localBits_setQBit {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (i : Fin k) (d : Fin 2) (s : Fin (2 ^ N)) :
    localBits addr (setQBit N (addr i) d s).val =
      Function.update (localBits addr s.val) i (d.val : ZMod 2) := by
  funext j
  by_cases hji : j = i
  · rw [hji, Function.update_self]
    change ((qBit (addr i) (setQBit N (addr i) d s).val).val : ZMod 2) = (d.val : ZMod 2)
    rw [qBit_setQBit_self (hlt i) d s]
  · rw [Function.update_of_ne hji]
    change ((qBit (addr j) (setQBit N (addr i) d s).val).val : ZMod 2) =
      ((qBit (addr j) s.val).val : ZMod 2)
    rw [qBit_setQBit_of_ne (fun h => hji (haddr h)) d s]

/-- The fiber index does not see prior changes at addressed qubits. -/
private theorem fiberIndex_setQBit {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (i : Fin k) (d : Fin 2) (s : Fin (2 ^ N)) (x : Fin k → ZMod 2) :
    fiberIndex addr (setQBit N (addr i) d s) x = fiberIndex addr s x := by
  have hL : localBits addr (fiberIndex addr (setQBit N (addr i) d s) x).val = x :=
    fiberIndex_localBits haddr hlt _ _
  have hR : localBits addr (fiberIndex addr s x).val = x :=
    fiberIndex_localBits haddr hlt _ _
  have h1 := fiberIndex_agree addr (setQBit N (addr i) d s) x
  have hmid : ∀ q : ℕ, (∀ j : Fin k, addr j ≠ q) →
      qBit q (setQBit N (addr i) d s).val = qBit q s.val := by
    intro q hq
    exact qBit_setQBit_of_ne (fun h => hq i h.symm) d s
  have h3 := fiberIndex_agree addr s x
  have hchain := agree_trans addr _ _ _ (agree_symm addr _ _ h1) (agree_trans addr _ _ _ hmid h3)
  have hbits : localBits addr (fiberIndex addr (setQBit N (addr i) d s) x).val =
      localBits addr (fiberIndex addr s x).val := hL.trans hR.symm
  exact eq_of_agree hchain hbits
/-- An embedded gate acts as the fiber action of its matrix. -/
private theorem applyGate_embeddedGate_eq_qAct {N q p : ℕ}
    (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    (hqp : q ≠ p) (hqN : q < N) (hpN : p < N) (φ : Fin (2 ^ N) → ℂ) :
    applyGate N (embeddedGate U q p) φ = qAct N q (complexOfGRatMatrix U) φ := by
  funext s
  have hg := embeddedGate_wellFormed U hU hqp hqN hpN
  rw [applyGate_embeddedGate hg φ s]
  rfl

/-- The ancilla phase commutes with an action elsewhere. -/
private theorem zAnc_qAct {N q anc : ℕ} (hqa : q ≠ anc)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin (2 ^ N) → ℂ) :
    zAnc N anc (qAct N q A φ) = qAct N q A (zAnc N anc φ) := by
  funext s
  simp only [zAnc, qAct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hqbit : qBit anc (setQBit N q d s).val = qBit anc s.val :=
    qBit_setQBit_of_ne hqa.symm d s
  rw [hqbit]
  ring
/-- Composition of one-qubit fiber actions multiplies the matrices. -/
private theorem qAct_qAct {N q : ℕ} (hq : q < N)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin (2 ^ N) → ℂ) :
    qAct N q A (qAct N q B φ) = qAct N q (A * B) φ := by
  funext s
  simp only [qAct, qBit_setQBit_self hq, setQBit_setQBit hq, Finset.mul_sum,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

/-- Adjoint of a one-qubit fiber action under the state dot product. -/
private theorem star_qAct_dotProduct {N q : ℕ} (hq : q < N)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (φ ψ : Fin (2 ^ N) → ℂ) :
    star (qAct N q A φ) ⬝ᵥ ψ = star φ ⬝ᵥ qAct N q (star A) ψ := by
  classical
  set e : Fin (2 ^ N) × Fin 2 → Fin (2 ^ N) × Fin 2 :=
    fun p => (setQBit N q p.2 p.1, qBit q p.1.val) with he
  have hinv : Function.Involutive e := by
    intro p
    obtain ⟨s, d⟩ := p
    simp only [he, qBit_setQBit_self hq, setQBit_setQBit hq, setQBit_qBit]
  set E : Fin (2 ^ N) × Fin 2 ≃ Fin (2 ^ N) × Fin 2 := ⟨e, e, hinv, hinv⟩ with hE
  have hLHS : star (qAct N q A φ) ⬝ᵥ ψ
      = ∑ p : Fin (2 ^ N) × Fin 2,
          star (A (qBit q p.1.val) p.2 * φ (setQBit N q p.2 p.1)) * ψ p.1 := by
    simp only [dotProduct, Pi.star_apply, qAct, star_sum, Finset.sum_mul]
    rw [← Fintype.sum_prod_type (fun p : Fin (2 ^ N) × Fin 2 =>
      star (A (qBit q p.1.val) p.2 * φ (setQBit N q p.2 p.1)) * ψ p.1)]
  have hRHS : star φ ⬝ᵥ qAct N q (star A) ψ
      = ∑ p : Fin (2 ^ N) × Fin 2,
          star (φ p.1) * ((star A) (qBit q p.1.val) p.2 * ψ (setQBit N q p.2 p.1)) := by
    simp only [dotProduct, Pi.star_apply, qAct, Finset.mul_sum]
    rw [← Fintype.sum_prod_type (fun p : Fin (2 ^ N) × Fin 2 =>
      star (φ p.1) * ((star A) (qBit q p.1.val) p.2 * ψ (setQBit N q p.2 p.1)))]
  rw [hLHS, hRHS, ← Equiv.sum_comp E]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  obtain ⟨s, d⟩ := p
  simp only [hE, Equiv.coe_fn_mk, he, qBit_setQBit_self hq, setQBit_setQBit hq,
    setQBit_qBit, star_mul, Matrix.star_apply]
  ring

/-- Action of an embedded operator on a state, as a fiber sum. -/
private theorem embedLocal_mulVec_apply {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (A : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) (φ : Fin (2 ^ N) → ℂ)
    (s : Fin (2 ^ N)) :
    (embedLocal N addr A *ᵥ φ) s =
      ∑ x, A (localBits addr s.val) x * φ (fiberIndex addr s x) := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [embedLocal]
  set F : Fin (2 ^ N) → ℂ := fun u =>
      (if (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
        then A (localBits addr s.val) (localBits addr u.val) else 0) * φ u with hF
  have hvan : ∀ u ∈ (Finset.univ : Finset (Fin (2 ^ N))),
      u ∉ Finset.image (fiberIndex addr s) Finset.univ → F u = 0 := by
    intro u _ hu
    by_cases h1 : (∀ q : ℕ, (∀ i, addr i ≠ q) → qBit q s.val = qBit q u.val)
    · exfalso
      apply hu
      rw [Finset.mem_image]
      exact ⟨localBits addr u.val, Finset.mem_univ _,
        (fiberIndex_cover haddr hlt s u h1).symm⟩
    · simp only [hF]
      rw [ite_eq_right h1, zero_mul]
  have hsub : ∑ u ∈ Finset.image (fiberIndex addr s) Finset.univ, F u
      = ∑ u ∈ Finset.univ, F u :=
    Finset.sum_subset (Finset.subset_univ _) hvan
  rw [← hsub]
  have hinj : Set.InjOn (fiberIndex addr s)
      ↑(Finset.univ : Finset (Fin k → ZMod 2)) :=
    fun x _ y _ hxy => fiberIndex_injective haddr hlt s hxy
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro x _
  have h1 := fiberIndex_agree addr s x
  have hLx : localBits addr (fiberIndex addr s x).val = x :=
    fiberIndex_localBits haddr hlt s x
  simp only [hF]
  rw [ite_eq_left h1, hLx]

/-- Action of the embedded Pauli string on a state, single fiber term. -/
private theorem pauliEmb_mulVec_apply {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (a b : Fin k → ZMod 2) (φ : Fin (2 ^ N) → ℂ) (s : Fin (2 ^ N)) :
    (pauliEmb N addr a b *ᵥ φ) s =
      hermPauli a b (localBits addr s.val) (localBits addr s.val + a) *
        φ (fiberIndex addr s (localBits addr s.val + a)) := by
  simp only [pauliEmb]
  rw [embedLocal_mulVec_apply haddr hlt]
  refine Finset.sum_eq_single (localBits addr s.val + a) ?_ ?_
  · intro x _ hx
    have hne : localBits addr s.val ≠ x + a := by
      intro hcon
      apply hx
      have haa : a + a = 0 := funext fun i => CharTwo.add_self_eq_zero (a i)
      have hcalc : localBits addr s.val + a = x := by
        rw [hcon, add_assoc, haa, add_zero]
      exact hcalc.symm
    have hzero : hermPauli a b (localBits addr s.val) x = 0 := by
      simp only [hermPauli, Matrix.smul_apply, smul_eq_mul,
        MathlibExt.Quantum.PauliXZ.pauliXZ_apply, ite_eq_right hne, mul_zero]
    rw [hzero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon
/-- Peel one letter off the embedded Pauli action at its own qubit. -/
private theorem pauliEmb_peel {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (i : Fin k) (a b : Fin k → ZMod 2) (φ : Fin (2 ^ N) → ℂ) :
    pauliEmb N addr a b *ᵥ φ =
      qAct N (addr i) (letterMat (a i) (b i))
        (pauliEmb N addr (Function.update a i 0) (Function.update b i 0) *ᵥ φ) := by
  have hSurj : ∀ c : ZMod 2, ∃ d : Fin 2, (d.val : ZMod 2) = c := by decide
  funext s
  simp only [qAct, pauliEmb_mulVec_apply haddr hlt,
    localBits_setQBit haddr hlt, fiberIndex_setQBit haddr hlt]
  set loc := localBits addr s.val with hloc
  obtain ⟨d₀, hd₀cast⟩ : ∃ d : Fin 2, (d.val : ZMod 2) = loc i + a i :=
    hSurj (loc i + a i)
  have h0letter : ∀ d : Fin 2, d ≠ d₀ →
      letterMat (a i) (b i) (qBit (addr i) s.val) d = 0 := by
    intro d hd
    have hcon : ¬ ((qBit (addr i) s.val).val : ZMod 2) =
        (d.val : ZMod 2) + a i := by
      intro hcon
      have h2 : (d.val : ZMod 2) + a i + a i = (d.val : ZMod 2) := by
        rw [add_assoc, CharTwo.add_self_eq_zero (a i), add_zero]
      have hdc : (d.val : ZMod 2) = loc i + a i := by
        calc (d.val : ZMod 2)
            = (d.val : ZMod 2) + a i + a i := h2.symm
          _ = ((qBit (addr i) s.val).val : ZMod 2) + a i := by rw [← hcon]
          _ = loc i + a i := rfl
      have heq : d = d₀ :=
        pauliComm_qBitCast_inj
          (show ((d.val : ℕ) : ZMod 2) = (d₀.val : ZMod 2) by rw [hdc, hd₀cast])
      exact hd heq
    rw [letterMat_apply, ite_eq_right hcon]
  rw [Finset.sum_eq_single_of_mem d₀ (Finset.mem_univ d₀)
    (fun d _ hd => by rw [h0letter d hd, zero_mul])]
  have hloc_eq : loc i = ((qBit (addr i) s.val).val : ZMod 2) := rfl
  have hcond₀ : ((qBit (addr i) s.val).val : ZMod 2) =
      (d₀.val : ZMod 2) + a i := by
    rw [hd₀cast, add_assoc, CharTwo.add_self_eq_zero (a i), add_zero, hloc_eq]
  have hLetter : letterMat (a i) (b i) (qBit (addr i) s.val) d₀ =
      Complex.I ^ ((a i).val * (b i).val) *
        (-1 : ℂ) ^ ((b i) * (d₀.val : ZMod 2)).val := by
    rw [letterMat_apply, ite_eq_left hcond₀]
  have hside : loc = loc + a + a := by
    funext j
    change loc j = (loc j + a j) + a j
    rw [add_assoc, CharTwo.add_self_eq_zero (a j), add_zero]
  have hH : hermPauli a b loc (loc + a) =
      Complex.I ^ (∑ j, (a j).val * (b j).val) *
        (-1 : ℂ) ^ (dotProduct b (loc + a)).val := by
    simp only [hermPauli, Matrix.smul_apply, smul_eq_mul,
      MathlibExt.Quantum.PauliXZ.pauliXZ_apply]
    rw [ite_eq_left hside]
  have hub : Function.update loc i (d₀.val : ZMod 2) + Function.update a i 0
      = loc + a := by
    funext j
    by_cases hj : j = i
    · subst j
      change Function.update loc i (d₀.val : ZMod 2) i + Function.update a i 0 i
        = loc i + a i
      rw [Function.update_self _ _ _, Function.update_self _ _ _,
        add_zero, hd₀cast]
    · change Function.update loc i (d₀.val : ZMod 2) j + Function.update a i 0 j
        = loc j + a j
      rw [Function.update_of_ne hj _ _, Function.update_of_ne hj _ _]
  have hside' : Function.update loc i (d₀.val : ZMod 2) =
      (Function.update loc i (d₀.val : ZMod 2) + Function.update a i 0) +
        Function.update a i 0 := by
    funext j
    change Function.update loc i (d₀.val : ZMod 2) j =
      (Function.update loc i (d₀.val : ZMod 2) j +
        Function.update a i 0 j) + Function.update a i 0 j
    rw [add_assoc, CharTwo.add_self_eq_zero (Function.update a i 0 j), add_zero]
  have hH' : hermPauli (Function.update a i 0) (Function.update b i 0)
      (Function.update loc i (d₀.val : ZMod 2))
      (Function.update loc i (d₀.val : ZMod 2) + Function.update a i 0) =
      Complex.I ^ (∑ j, (Function.update a i 0 j).val *
        (Function.update b i 0 j).val) *
        (-1 : ℂ) ^ (dotProduct (Function.update b i 0)
          (Function.update loc i (d₀.val : ZMod 2) +
            Function.update a i 0)).val := by
    simp only [hermPauli, Matrix.smul_apply, smul_eq_mul,
      MathlibExt.Quantum.PauliXZ.pauliXZ_apply]
    rw [ite_eq_left hside']
  have hE2 : (∑ x ∈ Finset.univ.erase i, (a x).val * (b x).val) =
      ∑ x ∈ Finset.univ.erase i, (Function.update a i 0 x).val *
        (Function.update b i 0 x).val := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne hj' _ _, Function.update_of_ne hj' _ _]
  have hL : (∑ j, (a j).val * (b j).val) = (a i).val * (b i).val +
      ∑ x ∈ Finset.univ.erase i, (a x).val * (b x).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hR : (∑ j, (Function.update a i 0 j).val *
        (Function.update b i 0 j).val) =
      (Function.update a i 0 i).val * (Function.update b i 0 i).val +
        ∑ x ∈ Finset.univ.erase i, (Function.update a i 0 x).val *
          (Function.update b i 0 x).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hterm : (Function.update a i 0 i).val *
      (Function.update b i 0 i).val = 0 := by
    rw [Function.update_self _ _ _, Function.update_self _ _ _]
    decide
  have hSum : (∑ j, (a j).val * (b j).val) = (a i).val * (b i).val +
      ∑ j, (Function.update a i 0 j).val *
        (Function.update b i 0 j).val := by
    rw [hL, hR, hterm, zero_add, hE2]
  have hE : (∑ x ∈ Finset.univ.erase i, b x * (loc + a) x) =
      ∑ x ∈ Finset.univ.erase i,
        Function.update b i 0 x * (loc + a) x := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne hj' _ _]
  have hDL : dotProduct b (loc + a) = b i * (loc + a) i +
      ∑ x ∈ Finset.univ.erase i, b x * (loc + a) x := by
    change (∑ j, b j * (loc + a) j) = _
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hDR : dotProduct (Function.update b i 0) (loc + a) =
      Function.update b i 0 i * (loc + a) i +
        ∑ x ∈ Finset.univ.erase i,
          Function.update b i 0 x * (loc + a) x := by
    change (∑ j, Function.update b i 0 j * (loc + a) j) = _
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hzi : (loc + a) i = (d₀.val : ZMod 2) := by
    change loc i + a i = _
    exact hd₀cast.symm
  have hDot : dotProduct b (loc + a) =
      dotProduct (Function.update b i 0) (loc + a) +
        b i * (d₀.val : ZMod 2) := by
    rw [hDL, hDR]
    simp only [Function.update_self, zero_mul, zero_add]
    rw [hE, hzi]
    exact add_comm _ _
  have hPZ : (-1 : ℂ) ^ ((dotProduct b (loc + a)).val) =
      (-1 : ℂ) ^ ((dotProduct (Function.update b i 0) (loc + a)).val) *
        (-1 : ℂ) ^ ((b i * (d₀.val : ZMod 2)).val) := by
    rw [hDot, neg_one_pow_val_add]
  have hIW : Complex.I ^ (∑ j, (a j).val * (b j).val) =
      Complex.I ^ ((a i).val * (b i).val) *
        Complex.I ^ (∑ j, (Function.update a i 0 j).val *
          (Function.update b i 0 j).val) := by
    rw [hSum, pow_add]
  rw [hH, hH', hLetter, hub, hPZ, hIW]
  ring

/-- At a trivial letter, the embedded Pauli commutes with the
one-qubit action at that letter's qubit. -/
private theorem pauliEmb_qAct_comm {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (i : Fin k) (a b : Fin k → ZMod 2) (h0 : a i = 0 ∧ b i = 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin (2 ^ N) → ℂ) :
    pauliEmb N addr a b *ᵥ (qAct N (addr i) A φ) =
      qAct N (addr i) A (pauliEmb N addr a b *ᵥ φ) := by
  funext s
  have hqb : qBit (addr i) (fiberIndex addr s (localBits addr s.val + a)).val =
      qBit (addr i) s.val := by
    apply pauliComm_qBitCast_inj
    change ((qBit (addr i)
      (fiberIndex addr s (localBits addr s.val + a)).val).val : ZMod 2) = _
    have hloc : localBits addr
        (fiberIndex addr s (localBits addr s.val + a)).val =
        localBits addr s.val + a :=
      fiberIndex_localBits haddr hlt s (localBits addr s.val + a)
    have h1 := congrFun hloc i
    simp only [localBits] at h1
    rw [h1]
    simp only [Pi.add_apply, h0.1, add_zero, localBits]
  have hH : ∀ c : ZMod 2, hermPauli a b
      (Function.update (localBits addr s.val) i c)
      (Function.update (localBits addr s.val) i c + a) =
      hermPauli a b (localBits addr s.val) (localBits addr s.val + a) := by
    intro c
    have hcond1 : Function.update (localBits addr s.val) i c =
        (Function.update (localBits addr s.val) i c + a) + a := by
      ext j
      simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hcond2 : localBits addr s.val = (localBits addr s.val + a) + a := by
      ext j
      simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    simp only [hermPauli, Matrix.smul_apply, smul_eq_mul]
    congr 1
    rw [MathlibExt.Quantum.PauliXZ.pauliXZ_apply,
      MathlibExt.Quantum.PauliXZ.pauliXZ_apply, ite_eq_left hcond1,
      ite_eq_left hcond2]
    congr 1
    congr 1
    simp only [dotProduct, Pi.add_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      rw [h0.2, zero_mul, zero_mul]
    · rw [Function.update_of_ne hj]
  have hPt : ∀ d : Fin 2, setQBit N (addr i) d
      (fiberIndex addr s (localBits addr s.val + a)) =
      fiberIndex addr s
        (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a) := by
    intro d
    apply fin_eq_of_qBit_eq
    intro qq hqq
    by_cases hj : ∃ j, addr j = qq
    · obtain ⟨j, rfl⟩ := hj
      apply pauliComm_qBitCast_inj
      change ((qBit (addr j) (setQBit N (addr i) d
        (fiberIndex addr s (localBits addr s.val + a))).val).val : ZMod 2) =
        ((qBit (addr j) (fiberIndex addr s
          (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a)).val).val :
          ZMod 2)
      have hLs : localBits addr (setQBit N (addr i) d
          (fiberIndex addr s (localBits addr s.val + a))).val =
          Function.update (localBits addr s.val + a) i (d.val : ZMod 2) := by
        have h1 : localBits addr (setQBit N (addr i) d
            (fiberIndex addr s (localBits addr s.val + a))).val =
            Function.update (localBits addr
              (fiberIndex addr s (localBits addr s.val + a)).val) i
              (d.val : ZMod 2) :=
          localBits_setQBit haddr hlt i d (fiberIndex addr s (localBits addr s.val + a))
        rw [fiberIndex_localBits haddr hlt s (localBits addr s.val + a)] at h1
        exact h1
      have hLf : localBits addr (fiberIndex addr s
          (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a)).val =
          Function.update (localBits addr s.val) i (d.val : ZMod 2) + a :=
        fiberIndex_localBits haddr hlt s
          (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a)
      have e1 := congrFun hLs j
      have e2 := congrFun hLf j
      simp only [localBits] at e1 e2
      rw [e1, e2]
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Pi.add_apply, h0.1, add_zero]
      · simp only [Function.update_of_ne hji, Pi.add_apply]
    · have hoff : ∀ j, addr j ≠ qq := fun j h => hj ⟨j, h⟩
      have eL : qBit qq (setQBit N (addr i) d
          (fiberIndex addr s (localBits addr s.val + a))).val =
          qBit qq s.val := by
        rw [qBit_setQBit_of_ne (Ne.symm (hoff i))]
        exact (fiberIndex_agree addr s (localBits addr s.val + a) qq hoff).symm
      have eR : qBit qq (fiberIndex addr s
          (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a)).val =
          qBit qq s.val :=
        (fiberIndex_agree addr s
          (Function.update (localBits addr s.val) i (d.val : ZMod 2) + a) qq hoff).symm
      rw [eL, eR]
  rw [pauliEmb_mulVec_apply haddr hlt]
  simp only [qAct]
  simp only [pauliEmb_mulVec_apply haddr hlt]
  simp only [localBits_setQBit haddr hlt, fiberIndex_setQBit haddr hlt]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hPt d, hH, hqb]
  ring

private theorem pauliComm_cnot_qBit_off {N : ℕ} (c anc : ℕ) (u : Fin (2 ^ N))
    (qq : ℕ) (h : qq ≠ anc) :
    qBit qq (cnotIndex N c anc u).val = qBit qq u.val := by
  simp only [cnotIndex]
  split
  · exact qBit_flipBit_of_ne h u
  · rfl

private theorem pauliComm_cnot_localBits {N k anc : ℕ} {addr : Fin k → ℕ}
    (hne : ∀ i, addr i ≠ anc) (i : Fin k) (s : Fin (2 ^ N)) :
    localBits addr (cnotIndex N (addr i) anc s).val = localBits addr s.val := by
  ext j
  simp only [localBits]
  rw [pauliComm_cnot_qBit_off _ _ _ _ (hne j)]

private theorem pauliComm_qBit_fiber_trivial {N k : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (i : Fin k) (a b : Fin k → ZMod 2) (h0 : a i = 0 ∧ b i = 0)
    (s : Fin (2 ^ N)) :
    qBit (addr i) (fiberIndex addr s (localBits addr s.val + a)).val =
      qBit (addr i) s.val := by
  apply pauliComm_qBitCast_inj
  change ((qBit (addr i)
    (fiberIndex addr s (localBits addr s.val + a)).val).val : ZMod 2) = _
  have hloc : localBits addr
      (fiberIndex addr s (localBits addr s.val + a)).val =
      localBits addr s.val + a :=
    fiberIndex_localBits haddr hlt s (localBits addr s.val + a)
  have h1 := congrFun hloc i
  simp only [localBits] at h1
  rw [h1]
  simp only [Pi.add_apply, h0.1, add_zero, localBits]

private theorem pauliComm_cnot_fiber_point {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hne : ∀ i, addr i ≠ anc)
    (i : Fin k) (a b : Fin k → ZMod 2) (h0 : a i = 0 ∧ b i = 0)
    (s : Fin (2 ^ N)) :
    fiberIndex addr (cnotIndex N (addr i) anc s) (localBits addr s.val + a) =
      cnotIndex N (addr i) anc
        (fiberIndex addr s (localBits addr s.val + a)) := by
  have hbr : qBit (addr i) (fiberIndex addr s (localBits addr s.val + a)).val =
      qBit (addr i) s.val :=
    pauliComm_qBit_fiber_trivial haddr hlt i a b h0 s
  apply fin_eq_of_qBit_eq
  intro qq hqq
  by_cases hj : ∃ j, addr j = qq
  · obtain ⟨j, rfl⟩ := hj
    apply pauliComm_qBitCast_inj
    change ((qBit (addr j) (fiberIndex addr (cnotIndex N (addr i) anc s)
      (localBits addr s.val + a)).val).val : ZMod 2) =
      ((qBit (addr j) (cnotIndex N (addr i) anc
        (fiberIndex addr s (localBits addr s.val + a))).val).val : ZMod 2)
    have hLf : localBits addr (fiberIndex addr (cnotIndex N (addr i) anc s)
        (localBits addr s.val + a)).val = localBits addr s.val + a :=
      fiberIndex_localBits haddr hlt (cnotIndex N (addr i) anc s)
        (localBits addr s.val + a)
    have e1 := congrFun hLf j
    simp only [localBits] at e1
    rw [e1]
    have hqb : qBit (addr j) (cnotIndex N (addr i) anc
        (fiberIndex addr s (localBits addr s.val + a))).val =
        qBit (addr j) (fiberIndex addr s (localBits addr s.val + a)).val :=
      pauliComm_cnot_qBit_off _ _ _ _ (hne j)
    rw [hqb]
    have hLs : localBits addr
        (fiberIndex addr s (localBits addr s.val + a)).val =
        localBits addr s.val + a :=
      fiberIndex_localBits haddr hlt s (localBits addr s.val + a)
    have e2 := congrFun hLs j
    simp only [localBits] at e2
    rw [e2]
  · have hoff : ∀ j, addr j ≠ qq := fun j h => hj ⟨j, h⟩
    have eL : qBit qq (fiberIndex addr (cnotIndex N (addr i) anc s)
        (localBits addr s.val + a)).val =
        qBit qq (cnotIndex N (addr i) anc s).val :=
      (fiberIndex_agree addr (cnotIndex N (addr i) anc s) (localBits addr s.val + a)
        qq hoff).symm
    rw [eL]
    by_cases hqa : qq = anc
    · have hqa' : anc = qq := hqa.symm
      subst hqa'
      have hc1 : cnotIndex N (addr i) anc s =
          if qBit (addr i) s.val = 1 then flipBit N anc s else s := rfl
      have hc2 : cnotIndex N (addr i) anc
          (fiberIndex addr s (localBits addr s.val + a)) =
          if qBit (addr i) (fiberIndex addr s (localBits addr s.val + a)).val
            = 1 then
            flipBit N anc (fiberIndex addr s (localBits addr s.val + a))
          else fiberIndex addr s (localBits addr s.val + a) := rfl
      rw [hc1, hc2, hbr]
      by_cases hcond : qBit (addr i) s.val = 1
      · simp only [hcond, ↓reduceIte]
        have hanc : qBit anc
            (fiberIndex addr s (localBits addr s.val + a)).val =
            qBit anc s.val :=
          (fiberIndex_agree addr s (localBits addr s.val + a) anc hne).symm
        simp only [qBit_flipBit_self hqq]
        rw [hanc]
      · simp only [hcond, ↓reduceIte]
        exact fiberIndex_agree addr s (localBits addr s.val + a) anc hne
    · have eL2 : qBit qq (cnotIndex N (addr i) anc s).val = qBit qq s.val :=
        pauliComm_cnot_qBit_off _ _ _ _ hqa
      have eR : qBit qq (cnotIndex N (addr i) anc
          (fiberIndex addr s (localBits addr s.val + a))).val =
          qBit qq (fiberIndex addr s (localBits addr s.val + a)).val :=
        pauliComm_cnot_qBit_off _ _ _ _ hqa
      have eS : qBit qq (fiberIndex addr s (localBits addr s.val + a)).val =
          qBit qq s.val :=
        (fiberIndex_agree addr s (localBits addr s.val + a) qq hoff).symm
      rw [eL2, eR, eS]

/-- At a trivial letter, the embedded Pauli commutes with the CNOT
pullback into the ancilla. -/
private theorem pauliEmb_cnot_comm {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hne : ∀ i, addr i ≠ anc)
    (i : Fin k) (a b : Fin k → ZMod 2) (h0 : a i = 0 ∧ b i = 0)
    (φ : Fin (2 ^ N) → ℂ) :
    pauliEmb N addr a b *ᵥ (fun s => φ (cnotIndex N (addr i) anc s)) =
      fun s => (pauliEmb N addr a b *ᵥ φ) (cnotIndex N (addr i) anc s) := by
  funext s
  show (pauliEmb N addr a b *ᵥ (fun s => φ (cnotIndex N (addr i) anc s))) s =
    (pauliEmb N addr a b *ᵥ φ) (cnotIndex N (addr i) anc s)
  rw [pauliEmb_mulVec_apply haddr hlt]
  rw [pauliEmb_mulVec_apply haddr hlt]
  rw [pauliComm_cnot_localBits hne]
  rw [pauliComm_cnot_fiber_point haddr hlt hne i a b h0 s]

/-- Real part of a star-dot product as a sum. -/
private theorem starDot_re_sum {N : ℕ} (φ ψ : Fin (2 ^ N) → ℂ) :
    (star φ ⬝ᵥ ψ).re = ∑ s, (starRingEnd ℂ (φ s) * ψ s).re := by
  change (∑ s, star φ s * ψ s).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Pi.star_apply, ← starRingEnd_apply]

/-- The ancilla-`1` weight from the tracked correlation. -/
private theorem ancProb_eq_ancCorr {N k anc : ℕ} {addr : Fin k → ℕ}
    (φ : Fin (2 ^ N) → ℂ) :
    (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (φ s) * φ s).re else 0) =
      (sqNorm φ - (ancCorr anc addr 0 0 φ).re) / 2 := by
  set P1 := ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
    (starRingEnd ℂ (φ s) * φ s).re else 0 with hP1
  set P0 := ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then (0 : ℝ) else
    (starRingEnd ℂ (φ s) * φ s).re with hP0
  have hSq : sqNorm φ = P0 + P1 := by
    rw [sqNorm_eq_re_star_dotProduct, starDot_re_sum]
    rw [hP0, hP1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : qBit anc s.val = 1 <;> simp [h]
  have hC : (ancCorr anc addr 0 0 φ).re = P0 - P1 := by
    have hP : pauliEmb N addr 0 0 = 1 := pauliEmb_zero_zero
    simp only [ancCorr, hP, Matrix.one_mulVec]
    rw [starDot_re_sum]
    rw [hP0, hP1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : qBit anc s.val = 1
    · have hz : zAnc N anc φ s = (-1 : ℂ) * φ s := by simp [zAnc, h]
      rw [hz]
      simp only [ite_eq_left h]
      have hneg : starRingEnd ℂ (φ s) * ((-1 : ℂ) * φ s) =
          -(starRingEnd ℂ (φ s) * φ s) := by ring
      rw [hneg, Complex.neg_re]
      ring
    · have hz : zAnc N anc φ s = (1 : ℂ) * φ s := by simp [zAnc, h]
      rw [hz]
      simp only [one_mul, ite_eq_right h, sub_zero]
  rw [hSq, hC]
  ring

/-- On a clean ancilla the correlation is the plain expectation. -/
private theorem ancCorr_clean {N k anc : ℕ} {addr : Fin k → ℕ}
    {a b : Fin k → ZMod 2} {ψ : Fin (2 ^ N) → ℂ}
    (hclean : ∀ s : Fin (2 ^ N), qBit anc s.val = 1 → ψ s = 0) :
    ancCorr anc addr a b ψ = star ψ ⬝ᵥ (pauliEmb N addr a b *ᵥ ψ) := by
  simp only [ancCorr]
  change (∑ s, star ψ s * zAnc N anc (pauliEmb N addr a b *ᵥ ψ) s) =
    ∑ s, star ψ s * (pauliEmb N addr a b *ᵥ ψ) s
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : qBit anc s.val = 1
  · have h0 : star ψ s = 0 := by
      rw [Pi.star_apply, hclean s h]
      exact star_zero ℂ
    rw [h0, zero_mul, zero_mul]
  · have hz : zAnc N anc (pauliEmb N addr a b *ᵥ ψ) s =
        (pauliEmb N addr a b *ᵥ ψ) s := by
      simp [zAnc, h]
    rw [hz]

/-- The sign `X` on the ancilla complements its `1`-weight. -/
private theorem ancProb_embeddedX {N anc : ℕ} (hanc0 : 0 < anc) (hanc : anc < N)
    (φ : Fin (2 ^ N) → ℂ) :
    (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (applyGate N (embeddedGate xGate anc 0) φ s) *
          applyGate N (embeddedGate xGate anc 0) φ s).re else 0) =
      sqNorm φ - ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (φ s) * φ s).re else 0 := by
  have hqp : anc ≠ 0 := ne_of_gt hanc0
  have hpN : 0 < N := lt_trans hanc0 hanc
  have hgate : ∀ s : Fin (2 ^ N),
      applyGate N (embeddedGate xGate anc 0) φ s = φ (flipBit N anc s) :=
    fun s => applyGate_embeddedGate_xGate hqp hanc hpN φ s
  have hinvF : Function.Involutive (flipBit N anc) :=
    fun s => flipBit_flipBit N anc s
  set P1 := ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
    (starRingEnd ℂ (φ s) * φ s).re else 0 with hP1
  set P0 := ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then (0 : ℝ) else
    (starRingEnd ℂ (φ s) * φ s).re with hP0
  have hSq : sqNorm φ = P0 + P1 := by
    rw [sqNorm_eq_re_star_dotProduct, starDot_re_sum]
    rw [hP0, hP1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : qBit anc s.val = 1 <;> simp [h]
  have hLHS : (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (applyGate N (embeddedGate xGate anc 0) φ s) *
          applyGate N (embeddedGate xGate anc 0) φ s).re else 0) = P0 := by
    have hF : (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
          (starRingEnd ℂ (applyGate N (embeddedGate xGate anc 0) φ s) *
            applyGate N (embeddedGate xGate anc 0) φ s).re else 0) =
        ∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
          (starRingEnd ℂ (φ (flipBit N anc s)) * φ (flipBit N anc s)).re else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [hgate s]
    rw [hF]
    have hre : (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
          (starRingEnd ℂ (φ (flipBit N anc s)) * φ (flipBit N anc s)).re else 0) =
        ∑ t : Fin (2 ^ N), (fun s => if qBit anc s.val = 1 then
          (starRingEnd ℂ (φ (flipBit N anc s)) * φ (flipBit N anc s)).re else 0)
          (Function.Involutive.toPerm (flipBit N anc) hinvF t) :=
      (Equiv.sum_comp (Function.Involutive.toPerm (flipBit N anc) hinvF) _).symm
    rw [hre, hP0]
    apply Finset.sum_congr rfl
    intro t _
    change (if qBit anc (flipBit N anc t).val = 1 then
        (starRingEnd ℂ (φ (flipBit N anc (flipBit N anc t))) *
          φ (flipBit N anc (flipBit N anc t))).re else 0) =
      (if qBit anc t.val = 1 then (0 : ℝ) else (starRingEnd ℂ (φ t) * φ t).re)
    have hff : flipBit N anc (flipBit N anc t) = t := flipBit_flipBit N anc t
    rw [hff]
    have hself := qBit_flipBit_self hanc t
    rw [hself]
    rcases fin2_dichot (qBit anc t.val) with hb | hb
    · rw [hb, ite_eq_left (by decide : ((0 : Fin 2) + 1) = 1),
        ite_eq_right (by decide : ¬((0 : Fin 2) = 1))]
    · rw [hb, ite_eq_right (by decide : ¬(((1 : Fin 2) + 1) = 1)),
        ite_eq_left (by decide : (1 : Fin 2) = 1)]
  rw [hLHS, hSq]
  ring

/-- One CNOT step updates the tracked label's `b` at its letter. -/
private theorem ancCorr_cnot {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    (i : Fin k) (a b : Fin k → ZMod 2) (h0 : a i = 0 ∧ b i = 0)
    (Φ : Fin (2 ^ N) → ℂ) :
    ancCorr anc addr a b (applyGate N (controlledGate xGate (addr i) anc) Φ) =
      ancCorr anc addr a (Function.update b i 1) Φ := by
  have hgate : ∀ s : Fin (2 ^ N),
      applyGate N (controlledGate xGate (addr i) anc) Φ s =
        Φ (cnotIndex N (addr i) anc s) :=
    fun s => applyGate_cnot (hne i) (hlt i) hanc Φ s
  have hgate_fun : applyGate N (controlledGate xGate (addr i) anc) Φ =
      fun s => Φ (cnotIndex N (addr i) anc s) := funext hgate
  have hinvC : Function.Involutive (cnotIndex N (addr i) anc) :=
    fun s => cnotIndex_cnotIndex (hne i) s
  have hqbit_cnot : ∀ t : Fin (2 ^ N),
      qBit anc (cnotIndex N (addr i) anc t).val =
        qBit anc t.val + qBit (addr i) t.val := by
    intro t
    simp only [cnotIndex]
    by_cases hc : qBit (addr i) t.val = 1
    · rw [ite_eq_left hc, qBit_flipBit_self hanc, hc]
    · rw [ite_eq_right hc]
      have h0c : qBit (addr i) t.val = 0 := by
        rcases fin2_dichot (qBit (addr i) t.val) with h' | h'
        · exact h'
        · exact absurd h' hc
      rw [h0c, add_zero]
  have hsign : ∀ t : Fin (2 ^ N),
      (if qBit anc (cnotIndex N (addr i) anc t).val = 1 then (-1 : ℂ) else 1) =
        (if qBit anc t.val = 1 then (-1 : ℂ) else 1) *
          (-1 : ℂ) ^ ((qBit (addr i) t.val).val) := by
    intro t
    rw [hqbit_cnot t]
    have hv0 : (0 : Fin 2).val = 0 := by decide
    have hv1 : (1 : Fin 2).val = 1 := by decide
    rcases fin2_dichot (qBit anc t.val) with ha | ha <;>
      rcases fin2_dichot (qBit (addr i) t.val) with hc | hc
    · rw [ha, hc, ite_eq_right (by decide : ¬(((0 : Fin 2) + (0 : Fin 2)) = 1)),
        ite_eq_right (by decide : ¬((0 : Fin 2) = 1)), hv0]
      simp
    · rw [ha, hc, ite_eq_left (by decide : ((0 : Fin 2) + (1 : Fin 2)) = 1),
        ite_eq_right (by decide : ¬((0 : Fin 2) = 1)), hv1]
      simp
    · rw [ha, hc, ite_eq_left (by decide : ((1 : Fin 2) + (0 : Fin 2)) = 1),
        ite_eq_left (by decide : (1 : Fin 2) = 1), hv0]
      simp
    · rw [ha, hc, ite_eq_right (by decide : ¬(((1 : Fin 2) + (1 : Fin 2)) = 1)),
        ite_eq_left (by decide : (1 : Fin 2) = 1), hv1]
      simp
  have hdotsplit : ∀ M : Fin k → ZMod 2,
      (Function.update b i 1) ⬝ᵥ M = M i + b ⬝ᵥ M := by
    intro M
    change (∑ j, Function.update b i 1 j * M j) = M i + ∑ j, b j * M j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have herase : (∑ x ∈ Finset.univ.erase i, Function.update b i 1 x * M x) =
        ∑ x ∈ Finset.univ.erase i, b x * M x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxne : x ≠ i := (Finset.mem_erase.mp hx).1
      rw [Function.update_of_ne hxne]
    rw [Function.update_self, h0.2, herase]
    simp
  have hIsum : (∑ j, (a j).val * ((Function.update b i 1) j).val) =
      ∑ j, (a j).val * (b j).val := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self, h0.1]
    · rw [Function.update_of_ne hj]
  have hLi : ∀ t : Fin (2 ^ N),
      localBits addr t.val i = ((qBit (addr i) t.val).val : ZMod 2) :=
    fun t => rfl
  simp only [ancCorr]
  rw [hgate_fun, pauliEmb_cnot_comm haddr hlt hne i a b h0 Φ]
  change (∑ s, star (Φ (cnotIndex N (addr i) anc s)) *
      ((if qBit anc s.val = 1 then (-1 : ℂ) else 1) *
        (pauliEmb N addr a b *ᵥ Φ) (cnotIndex N (addr i) anc s))) =
    ∑ s, star (Φ s) *
      ((if qBit anc s.val = 1 then (-1 : ℂ) else 1) *
        (pauliEmb N addr a (Function.update b i 1) *ᵥ Φ) s)
  have hre : (∑ s, star (Φ (cnotIndex N (addr i) anc s)) *
      ((if qBit anc s.val = 1 then (-1 : ℂ) else 1) *
        (pauliEmb N addr a b *ᵥ Φ) (cnotIndex N (addr i) anc s))) =
      ∑ t, (fun s => star (Φ (cnotIndex N (addr i) anc s)) *
        ((if qBit anc s.val = 1 then (-1 : ℂ) else 1) *
          (pauliEmb N addr a b *ᵥ Φ) (cnotIndex N (addr i) anc s)))
        (Function.Involutive.toPerm (cnotIndex N (addr i) anc) hinvC t) :=
    (Equiv.sum_comp (Function.Involutive.toPerm (cnotIndex N (addr i) anc) hinvC) _).symm
  rw [hre]
  apply Finset.sum_congr rfl
  intro t _
  change (star (Φ (cnotIndex N (addr i) anc (cnotIndex N (addr i) anc t))) *
      ((if qBit anc (cnotIndex N (addr i) anc t).val = 1 then (-1 : ℂ) else 1) *
        (pauliEmb N addr a b *ᵥ Φ)
          (cnotIndex N (addr i) anc (cnotIndex N (addr i) anc t)))) =
    (star (Φ t) *
      ((if qBit anc t.val = 1 then (-1 : ℂ) else 1) *
        (pauliEmb N addr a (Function.update b i 1) *ᵥ Φ) t))
  rw [cnotIndex_cnotIndex (hne i) t]
  rw [hsign t]
  rw [pauliEmb_mulVec_apply haddr hlt a b Φ t,
    pauliEmb_mulVec_apply haddr hlt a (Function.update b i 1) Φ t]
  have hMi : (localBits addr t.val + a) i = localBits addr t.val i := by
    simp [h0.1]
  have hratio : (-1 : ℂ) ^ ((qBit (addr i) t.val).val) *
      hermPauli a b (localBits addr t.val) (localBits addr t.val + a) =
      hermPauli a (Function.update b i 1) (localBits addr t.val)
        (localBits addr t.val + a) := by
    simp only [hermPauli, Matrix.smul_apply, smul_eq_mul,
      MathlibExt.Quantum.PauliXZ.pauliXZ_apply]
    by_cases hc : localBits addr t.val = (localBits addr t.val + a) + a
    · simp only [ite_eq_left hc]
      rw [hdotsplit, hMi, neg_one_pow_val_add, hLi t, fin2_cast_val, hIsum]
      ring
    · simp only [ite_eq_right hc, mul_zero]
  rw [← hratio]
  ring

/-- Conjugation step: a one-qubit action at a letter's qubit
conjugates the tracked label's letter there. -/
private theorem ancCorr_qAct {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hne : ∀ i, addr i ≠ anc) (i : Fin k) (U : Matrix (Fin 2) (Fin 2) ℂ)
    {a1 b1 a2 b2 : Fin k → ZMod 2}
    (hoff : ∀ j, j ≠ i → a1 j = a2 j ∧ b1 j = b2 j)
    (hrel : star U * letterMat (a2 i) (b2 i) * U = letterMat (a1 i) (b1 i))
    (Φ : Fin (2 ^ N) → ℂ) :
    ancCorr anc addr a2 b2 (qAct N (addr i) U Φ) =
      ancCorr anc addr a1 b1 Φ := by
  unfold ancCorr
  rw [pauliEmb_peel haddr hlt i]
  have h0' : (Function.update a2 i 0) i = 0 ∧ (Function.update b2 i 0) i = 0 := by
    simp
  rw [pauliEmb_qAct_comm haddr hlt i (Function.update a2 i 0)
    (Function.update b2 i 0) h0']
  rw [zAnc_qAct (hne i)]
  rw [zAnc_qAct (hne i)]
  rw [qAct_qAct (hlt i)]
  rw [star_qAct_dotProduct (hlt i)]
  rw [qAct_qAct (hlt i)]
  rw [← Matrix.mul_assoc, hrel]
  rw [← zAnc_qAct (hne i)]
  have ha_eq : Function.update a1 i 0 = Function.update a2 i 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, (hoff j hj).1]
  have hb_eq : Function.update b1 i 0 = Function.update b2 i 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, (hoff j hj).2]
  rw [← ha_eq, ← hb_eq]
  rw [← pauliEmb_peel haddr hlt i]

/-- One full letter of the core updates the tracked label. -/
private theorem ancCorr_letter {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    (a b a' b' : Fin k → ZMod 2) (i : Fin k) (h0 : a' i = 0 ∧ b' i = 0)
    (Φ : Fin (2 ^ N) → ℂ) :
    ancCorr anc addr a' b'
        (applyCircuit N (basisChangeGates (a i) (b i) (addr i) anc ++
          parityGates (a i) (b i) (addr i) anc) Φ) =
      ancCorr anc addr (Function.update a' i (a i)) (Function.update b' i (b i)) Φ := by
  have ha := zmod2_dichot (a i)
  have hb := zmod2_dichot (b i)
  rcases ha with hai0 | hai1
  · rcases hb with hbi0 | hbi1
    · -- (0,0): both lists empty
      rw [hai0, hbi0]
      have hbG : basisChangeGates (0 : ZMod 2) 0 (addr i) anc = [] := by
        simp [basisChangeGates]
      have hpG : parityGates (0 : ZMod 2) 0 (addr i) anc = [] := by
        simp [parityGates]
      rw [hbG, hpG]
      change ancCorr anc addr a' b' Φ = _
      have ha_upd : Function.update a' i (0 : ZMod 2) = a' := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [h0.1]
        · simp [hj]
      have hb_upd : Function.update b' i (0 : ZMod 2) = b' := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [h0.2]
        · simp [hj]
      rw [ha_upd, hb_upd]
    · -- (0,1): only the CNOT
      rw [hai0, hbi1]
      have hbG : basisChangeGates (0 : ZMod 2) 1 (addr i) anc = [] := by
        simp [basisChangeGates]
      have hpG : parityGates (0 : ZMod 2) 1 (addr i) anc =
          [controlledGate xGate (addr i) anc] := by
        simp [parityGates]
      rw [hbG, hpG]
      change ancCorr anc addr a' b'
        (applyGate N (controlledGate xGate (addr i) anc) Φ) = _
      rw [ancCorr_cnot haddr hlt hanc hne i a' b' h0 _]
      have ha_upd : Function.update a' i (0 : ZMod 2) = a' := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [h0.1]
        · simp [hj]
      rw [ha_upd]
  · rcases hb with hbi0 | hbi1
    · -- (1,0): ωH embedded then CNOT
      rw [hai1, hbi0]
      have hbG : basisChangeGates (1 : ZMod 2) 0 (addr i) anc =
          [embeddedGate omegaH (addr i) anc] := by
        simp [basisChangeGates]
      have hpG : parityGates (1 : ZMod 2) 0 (addr i) anc =
          [controlledGate xGate (addr i) anc] := by
        simp [parityGates]
      rw [hbG, hpG]
      change ancCorr anc addr a' b'
        (applyGate N (controlledGate xGate (addr i) anc)
          (applyGate N (embeddedGate omegaH (addr i) anc) Φ)) = _
      have hwH : applyGate N (embeddedGate omegaH (addr i) anc) Φ =
          qAct N (addr i) (complexOfGRatMatrix omegaH) Φ :=
        applyGate_embeddedGate_eq_qAct omegaH omegaH_unitary (hne i) (hlt i) hanc Φ
      rw [hwH]
      rw [ancCorr_cnot haddr hlt hanc hne i a' b' h0 _]
      have hoff : ∀ j, j ≠ i →
          (Function.update a' i 1) j = a' j ∧
            b' j = (Function.update b' i 1) j := by
        intro j hj; simp [hj]
      have hrel : star (complexOfGRatMatrix omegaH) *
          letterMat (a' i) ((Function.update b' i 1) i) *
          (complexOfGRatMatrix omegaH) =
          letterMat ((Function.update a' i 1) i) (b' i) := by
        have e1 : (Function.update b' i (1 : ZMod 2)) i = 1 := by simp
        have e2 : (Function.update a' i (1 : ZMod 2)) i = 1 := by simp
        rw [e1, e2, h0.1, h0.2]
        have hz : letterMat (0 : ZMod 2) 1 = !![1, 0; 0, -1] := by
          simp [letterMat]
        have hx : letterMat (1 : ZMod 2) 0 = !![0, 1; 1, 0] := by
          simp [letterMat]
        rw [hz, hx, ← complexOfGRatMatrix_zGate, ← complexOfGRatMatrix_xGate]
        exact omegaH_conj_zGate
      have hq := ancCorr_qAct haddr hlt hne i (complexOfGRatMatrix omegaH)
        (a1 := Function.update a' i 1) (b1 := b')
        (a2 := a') (b2 := Function.update b' i 1) hoff hrel Φ
      rw [hq]
      have hb_upd : Function.update b' i (0 : ZMod 2) = b' := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [h0.2]
        · simp [hj]
      rw [hb_upd]
    · -- (1,1): sDag then ωH embedded gates, then CNOT
      rw [hai1, hbi1]
      have hbG : basisChangeGates (1 : ZMod 2) 1 (addr i) anc =
          [embeddedGate sDagGate (addr i) anc,
            embeddedGate omegaH (addr i) anc] := by
        simp [basisChangeGates]
      have hpG : parityGates (1 : ZMod 2) 1 (addr i) anc =
          [controlledGate xGate (addr i) anc] := by
        simp [parityGates]
      rw [hbG, hpG]
      change ancCorr anc addr a' b'
        (applyGate N (controlledGate xGate (addr i) anc)
          (applyGate N (embeddedGate omegaH (addr i) anc)
            (applyGate N (embeddedGate sDagGate (addr i) anc) Φ))) = _
      have hsDag : applyGate N (embeddedGate sDagGate (addr i) anc) Φ =
          qAct N (addr i) (complexOfGRatMatrix sDagGate) Φ :=
        applyGate_embeddedGate_eq_qAct sDagGate sDagGate_unitary
          (hne i) (hlt i) hanc Φ
      rw [hsDag]
      have hwH : applyGate N (embeddedGate omegaH (addr i) anc)
          (qAct N (addr i) (complexOfGRatMatrix sDagGate) Φ) =
          qAct N (addr i) (complexOfGRatMatrix omegaH)
            (qAct N (addr i) (complexOfGRatMatrix sDagGate) Φ) :=
        applyGate_embeddedGate_eq_qAct omegaH omegaH_unitary
          (hne i) (hlt i) hanc _
      rw [hwH]
      rw [qAct_qAct (hlt i)]
      rw [ancCorr_cnot haddr hlt hanc hne i a' b' h0 _]
      have hoff : ∀ j, j ≠ i →
          (Function.update a' i 1) j = a' j ∧
            (Function.update b' i 1) j = (Function.update b' i 1) j := by
        intro j hj; simp [hj]
      have hrel : star (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) *
          letterMat (a' i) ((Function.update b' i 1) i) *
          (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate) =
          letterMat ((Function.update a' i 1) i)
            ((Function.update b' i 1) i) := by
        have e1 : (Function.update b' i (1 : ZMod 2)) i = 1 := by simp
        have e2 : (Function.update a' i (1 : ZMod 2)) i = 1 := by simp
        rw [e1, e2, h0.1]
        have hz : letterMat (0 : ZMod 2) 1 = !![1, 0; 0, -1] := by
          simp [letterMat]
        have hy : letterMat (1 : ZMod 2) 1 =
            !![0, -Complex.I; Complex.I, 0] := by
          simp [letterMat]
        rw [hz, hy, ← complexOfGRatMatrix_zGate]
        exact omegaH_sDag_conj_zGate
      have hq := ancCorr_qAct haddr hlt hne i
        (complexOfGRatMatrix omegaH * complexOfGRatMatrix sDagGate)
        (a1 := Function.update a' i 1) (b1 := Function.update b' i 1)
        (a2 := a') (b2 := Function.update b' i 1) hoff hrel Φ
      rw [hq]

/-- Induction invariant: processing a duplicate-free letter list
installs exactly those letters into the tracked label. -/
private theorem ancCorr_flatMap {N k anc : ℕ} {addr : Fin k → ℕ}
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    (a b : Fin k → ZMod 2) :
    ∀ (l : List (Fin k)), l.Nodup →
      ∀ (a' b' : Fin k → ZMod 2), (∀ j ∈ l, a' j = 0 ∧ b' j = 0) →
        ∀ (Φ : Fin (2 ^ N) → ℂ),
          ancCorr anc addr a' b'
              (applyCircuit N (l.flatMap (fun i =>
                basisChangeGates (a i) (b i) (addr i) anc ++
                  parityGates (a i) (b i) (addr i) anc)) Φ) =
            ancCorr anc addr (fun j => if j ∈ l then a j else a' j)
              (fun j => if j ∈ l then b j else b' j) Φ := by
  intro l
  induction l with
  | nil =>
    intro _ a' b' _ Φ
    simp only [List.flatMap_nil, applyCircuit, List.foldl_nil]
    have h1 : (fun j => if j ∈ ([] : List (Fin k)) then a j else a' j) = a' := by
      funext j
      simp
    have h2 : (fun j => if j ∈ ([] : List (Fin k)) then b j else b' j) = b' := by
      funext j
      simp
    rw [h1, h2]
  | cons i l ih =>
    intro hnod a' b' hz Φ
    rw [List.nodup_cons] at hnod
    obtain ⟨hinotl, hlnod⟩ := hnod
    have hzl : ∀ j ∈ l, a' j = 0 ∧ b' j = 0 :=
      fun j hj => hz j (List.mem_cons.mpr (Or.inr hj))
    simp only [List.flatMap_cons]
    rw [applyCircuit_append]
    have hIH := ih hlnod a' b' hzl
      (applyCircuit N
        (basisChangeGates (a i) (b i) (addr i) anc ++
          parityGates (a i) (b i) (addr i) anc) Φ)
    rw [hIH]
    have hai : a' i = 0 := (hz i (List.mem_cons.mpr (Or.inl rfl))).1
    have hbi : b' i = 0 := (hz i (List.mem_cons.mpr (Or.inl rfl))).2
    have h0AB : (fun j => if j ∈ l then a j else a' j) i = 0 ∧
        (fun j => if j ∈ l then b j else b' j) i = 0 := by
      simp [hinotl, hai, hbi]
    have hfold := ancCorr_letter haddr hlt hanc hne a b
      (fun j => if j ∈ l then a j else a' j)
      (fun j => if j ∈ l then b j else b' j) i h0AB Φ
    rw [hfold]
    have hA : Function.update (fun j => if j ∈ l then a j else a' j) i (a i) =
        (fun j => if j ∈ i :: l then a j else a' j) := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp [Function.update_self]
      · rw [Function.update_of_ne hji]
        simp only [List.mem_cons, hji, false_or]
    have hB : Function.update (fun j => if j ∈ l then b j else b' j) i (b i) =
        (fun j => if j ∈ i :: l then b j else b' j) := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp [Function.update_self]
      · rw [Function.update_of_ne hji]
        simp only [List.mem_cons, hji, false_or]
    rw [hA, hB]

/-- Core identity. Let the addresses `addr` be injective with every
`addr i < N`, and let the ancilla satisfy `0 < anc < N` and `addr i ≠ anc`
for every `i`. On a state with a clean ancilla (zero amplitude at every basis
state whose ancilla bit is `1`), the weight of the answer ancilla reading `1`
after the core is `(sqNorm ψ - σ ⟨ψ|P_emb|ψ⟩) / 2`, where `σ = -1` when `neg`
holds and `σ = 1` otherwise; it is a probability when `sqNorm ψ = 1`. -/
theorem ancProb_perLabelCore {N k anc : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) (neg : Bool)
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc0 : 0 < anc) (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    {ψ : Fin (2 ^ N) → ℂ}
    (hclean : ∀ s : Fin (2 ^ N), qBit anc s.val = 1 → ψ s = 0) :
    (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (applyCircuit N (perLabelCore addr a b neg anc) ψ s) *
          applyCircuit N (perLabelCore addr a b neg anc) ψ s).re else 0) =
      (sqNorm ψ - (if neg then -1 else 1) * pauliExpect addr a b ψ) / 2 := by
  unfold perLabelCore
  rw [applyCircuit_append]
  set Φflat : Fin (2 ^ N) → ℂ := applyCircuit N ((List.finRange k).flatMap (fun i =>
    basisChangeGates (a i) (b i) (addr i) anc ++
      parityGates (a i) (b i) (addr i) anc)) ψ with hΦ
  have hgs : ∀ g ∈ (List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc), QGateWellFormed N g := by
    intro g hg
    have hgmem : g ∈ perLabelCircuit addr a b neg anc := by
      simp only [perLabelCircuit, perLabelCore, List.mem_append]
      exact Or.inl (Or.inl hg)
    exact perLabelCircuit_wellFormed a b neg hlt hanc0 hanc hne g hgmem
  have hsq : sqNorm Φflat = sqNorm ψ := by
    rw [hΦ]
    exact sqNorm_applyCircuit hgs ψ
  have hcorr : ancCorr anc addr 0 0 Φflat =
      star ψ ⬝ᵥ (pauliEmb N addr a b *ᵥ ψ) := by
    have hfm := ancCorr_flatMap haddr hlt hanc hne a b (List.finRange k)
      (List.nodup_finRange k) 0 0 (fun _ _ => ⟨rfl, rfl⟩) ψ
    have ha : (fun j => if j ∈ List.finRange k then a j else (0 : Fin k → ZMod 2) j) = a := by
      funext j
      exact ite_eq_left (List.mem_finRange j)
    have hb : (fun j => if j ∈ List.finRange k then b j else (0 : Fin k → ZMod 2) j) = b := by
      funext j
      exact ite_eq_left (List.mem_finRange j)
    rw [hΦ, hfm, ha, hb, ancCorr_clean hclean]
  have hflat : (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
      (starRingEnd ℂ (Φflat s) * Φflat s).re else 0) =
      (sqNorm ψ - pauliExpect addr a b ψ) / 2 := by
    have h1 : (∑ s : Fin (2 ^ N), if qBit anc s.val = 1 then
        (starRingEnd ℂ (Φflat s) * Φflat s).re else 0) =
        (sqNorm Φflat - (ancCorr anc addr 0 0 Φflat).re) / 2 :=
      ancProb_eq_ancCorr _
    have hfold : (star ψ ⬝ᵥ (pauliEmb N addr a b *ᵥ ψ)).re =
        pauliExpect addr a b ψ := rfl
    rw [h1, hsq, hcorr, hfold]
  by_cases hn : neg = true
  · rw [ite_eq_left hn, ite_eq_left hn]
    simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
    have hx := ancProb_embeddedX hanc0 hanc Φflat
    rw [hx, hsq, hflat]
    ring
  · rw [ite_eq_right hn, ite_eq_right hn]
    simp only [applyCircuit, List.foldl_nil]
    rw [hflat]
    ring

/-- **Per-label expectation identity.** Let the addresses `addr` be
injective with every `addr i < N`, and let the ancilla satisfy
`0 < anc < N` and `addr i ≠ anc` for every `i`. On a state with a clean
ancilla (zero amplitude at every basis state whose ancilla bit is `1`), the
acceptance weight of the circuit is `(‖ψ‖² - σ ⟨ψ|P_emb|ψ⟩) / 2`, where
`σ = -1` when `neg` holds and `σ = 1` otherwise. It is a probability only
for a unit state, the case of `acceptProb_perLabelCircuit_signOne`. -/
theorem acceptProb_perLabelCircuit {N k anc : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) (neg : Bool)
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc0 : 0 < anc) (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    {ψ : Fin (2 ^ N) → ℂ}
    (hclean : ∀ s : Fin (2 ^ N), qBit anc s.val = 1 → ψ s = 0) :
    acceptProb (applyCircuit N (perLabelCircuit addr a b neg anc) ψ) =
      (sqNorm ψ - (if neg then -1 else 1) * pauliExpect addr a b ψ) / 2 := by
  unfold perLabelCircuit
  rw [applyCircuit_append]
  rw [acceptProb_outputSwap hanc0 hanc]
  exact ancProb_perLabelCore a b neg haddr hlt hanc0 hanc hne hclean

/-- For a unit state, the acceptance probability in `signOne` form (with
`signOne 0 = +1`), the shape consumed by the Pauli-test acceptance identity.
Let the addresses `addr` be injective with every `addr i < N`, let the
ancilla satisfy `0 < anc < N` and `addr i ≠ anc` for every `i`, and let `ψ`
have a clean ancilla (zero amplitude at every basis state whose ancilla bit
is `1`) and `sqNorm ψ = 1`. Then the circuit with sign `neg = (c < 0)`
accepts with probability `(1 - signOne c * ⟨ψ|P_emb|ψ⟩) / 2`. -/
theorem acceptProb_perLabelCircuit_signOne {N k anc : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) (c : ℝ)
    (haddr : Function.Injective addr) (hlt : ∀ i, addr i < N)
    (hanc0 : 0 < anc) (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    {ψ : Fin (2 ^ N) → ℂ} (hψ : sqNorm ψ = 1)
    (hclean : ∀ s : Fin (2 ^ N), qBit anc s.val = 1 → ψ s = 0) :
    acceptProb (applyCircuit N (perLabelCircuit addr a b (decide (c < 0)) anc) ψ) =
      (1 - signOne c * pauliExpect addr a b ψ) / 2 := by
  have h := acceptProb_perLabelCircuit a b (decide (c < 0))
    haddr hlt hanc0 hanc hne hclean
  rw [hψ] at h
  have hs : signOne c = if c < 0 then (-1 : ℝ) else 1 := by
    by_cases hc : c < 0
    · simp only [signOne, ite_eq_right (not_le.mpr hc), ite_eq_left hc]
    · simp only [signOne, ite_eq_left (le_of_not_gt hc), ite_eq_right hc]
  rw [hs]
  simpa only [decide_eq_true_eq] using h
/-- Accept-iff-`σ · parity = -1` on computational-basis inputs, for
`Z`-strings. Let every address `addr i` be below `N` (the addresses need not
be injective), and let the ancilla satisfy `0 < anc < N` and `addr i ≠ anc`
for every `i`. For a basis state `s` whose ancilla bit is `0`, the circuit
for the label `(0, b)` accepts `s` with probability `1` when
`σ · (-1) ^ (b · localBits addr s) = -1` and `0` otherwise, where `σ = -1`
when `neg` holds and `σ = 1` otherwise. -/
theorem acceptProb_perLabelCircuit_single_zString {N k anc : ℕ} {addr : Fin k → ℕ}
    (b : Fin k → ZMod 2) (neg : Bool)
    (hlt : ∀ i, addr i < N)
    (hanc0 : 0 < anc) (hanc : anc < N) (hne : ∀ i, addr i ≠ anc)
    (s : Fin (2 ^ N)) (hs : qBit anc s.val = 0) :
    acceptProb (applyCircuit N (perLabelCircuit addr 0 b neg anc) (Pi.single s 1)) =
      if (if neg then (-1 : ℝ) else 1) * (-1) ^ (b ⬝ᵥ localBits addr s.val).val = -1
        then 1 else 0 := by
  have h0N : 0 < N := Nat.lt_trans hanc0 hanc
  have hne2 : anc ≠ 0 := by omega
  have hbasis : ∀ i : Fin k, basisChangeGates 0 (b i) (addr i) anc = [] := by
    intro i
    unfold basisChangeGates
    simp [show (0 : ZMod 2) ≠ 1 by decide]
  unfold perLabelCircuit perLabelCore
  simp only [Pi.zero_apply]
  have hflat : (List.finRange k).flatMap (fun i =>
      basisChangeGates 0 (b i) (addr i) anc ++
        parityGates 0 (b i) (addr i) anc) =
      (List.finRange k).flatMap (fun i => parityGates 0 (b i) (addr i) anc) := by
    apply List.flatMap_congr
    intro i _
    rw [hbasis i, List.nil_append]
  rw [hflat]
  rw [applyCircuit_append, applyCircuit_append]
  have hcnot : ∀ (l : List (Fin k)) (s0 : Fin (2 ^ N)),
      (∀ i ∈ l, addr i < N ∧ addr i ≠ anc) →
      ∃ s1 : Fin (2 ^ N),
        applyCircuit N (l.flatMap (fun i => parityGates 0 (b i) (addr i) anc))
          (Pi.single s0 1) = Pi.single s1 1 ∧
        (∀ q : ℕ, q ≠ anc → qBit q s1.val = qBit q s0.val) ∧
        (((qBit anc s1.val).val : ZMod 2) =
          ((qBit anc s0.val).val : ZMod 2) +
            (List.map (fun i => b i * localBits addr s0.val i) l).sum) := by
    intro l s0 hl
    induction l generalizing s0 with
    | nil =>
      exact ⟨s0, by simp [applyCircuit], fun q _ => rfl, by simp⟩
    | cons i l ih =>
      simp only [List.flatMap_cons, applyCircuit_append] at ⊢
      have hhead : parityGates 0 (b i) (addr i) anc =
          (if b i = 0 then [] else [controlledGate xGate (addr i) anc]) := by
        unfold parityGates
        by_cases hb : b i = 0
        · simp [hb]
        · simp [hb]
      rw [hhead] at ⊢
      by_cases hb : b i = 0
      · simp only [hb, ite_true] at ⊢
        have hid : applyCircuit N [] (Pi.single s0 1) = Pi.single s0 1 := by
          simp only [applyCircuit, List.foldl_nil]
        rw [hid] at ⊢
        obtain ⟨s1, hs1, hq1, hpar1⟩ :=
          ih s0 (fun j hj => hl j (List.mem_cons_of_mem i hj))
        refine ⟨s1, hs1, hq1, ?_⟩
        simp only [List.map_cons, List.sum_cons, hb, zero_mul, zero_add] at ⊢
        exact hpar1
      · simp only [hb, ite_false] at ⊢
        have hone : applyCircuit N [controlledGate xGate (addr i) anc]
            (Pi.single s0 1) =
            applyGate N (controlledGate xGate (addr i) anc) (Pi.single s0 1) := by
          simp only [applyCircuit, List.foldl_cons, List.foldl_nil]
        rw [hone] at ⊢
        have hi := (hl i List.mem_cons_self).1
        have hn := (hl i List.mem_cons_self).2
        rw [applyGate_cnot_single hn hi hanc]
        obtain ⟨s1, hs1, hq1, hpar1⟩ :=
          ih (cnotIndex N (addr i) anc s0)
            (fun j hj => hl j (List.mem_cons_of_mem i hj))
        refine ⟨s1, ?_, ?_, ?_⟩
        · simp [hs1]
        · intro q hq
          rw [hq1 q hq]
          unfold cnotIndex
          by_cases h : qBit (addr i) s0.val = 1
          · simp [h, qBit_flipBit_of_ne hq]
          · simp [h]
        · simp only [hpar1, List.map_cons, List.sum_cons]
          unfold cnotIndex localBits
          by_cases h : qBit (addr i) s0.val = 1
          · have hbi : b i = 1 := (zmod2_dichot (b i)).resolve_left hb
            have hcast : ∀ x : Fin 2, (((x + 1).val : ℕ) : ZMod 2) =
                ((x.val : ℕ) : ZMod 2) + 1 := by
              intro x; fin_cases x <;> decide
            have hself : qBit anc (flipBit N anc s0).val = qBit anc s0.val + 1 :=
              qBit_flipBit_self hanc s0
            have hsum :
                (List.map (fun j => b j * ((qBit (addr j) (flipBit N anc s0).val).val : ZMod 2))
                  l).sum =
                  (List.map (fun j => b j * ((qBit (addr j) s0.val).val : ZMod 2)) l).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro j hj
              have hne : addr j ≠ anc := (hl j (List.mem_cons_of_mem i hj)).2
              have hq := qBit_flipBit_of_ne hne s0
              simp [hq]
            simp [h, hbi, hself, hcast, hsum]
            ring
          · have h0 : qBit (addr i) s0.val = 0 := (fin2_dichot _).resolve_right h
            simp [h0, mul_zero]
  obtain ⟨s1, hs1, hq1, hpar1⟩ := hcnot (List.finRange k) s
    (fun i _ => ⟨hlt i, hne i⟩)
  rw [hs1]
  have hsign : ∀ t0 : Fin (2 ^ N),
      applyCircuit N (if neg then [embeddedGate xGate anc 0] else [])
        (Pi.single t0 1) =
      Pi.single (if neg then flipBit N anc t0 else t0) 1 := by
    intro t0
    by_cases hn : neg = true
    · simp only [hn, ite_true, applyCircuit, List.foldl_cons, List.foldl_nil] at ⊢
      exact applyGate_embeddedGate_xGate_single hne2 hanc h0N t0
    · simp [hn, applyCircuit] at ⊢
  rw [hsign]
  have hswap_acc : ∀ t0 : Fin (2 ^ N),
      acceptProb (applyCircuit N [outputSwap anc] (Pi.single t0 1)) =
      (if qBit anc t0.val = 1 then 1 else 0 : ℝ) := by
    intro t0
    rw [acceptProb_outputSwap hanc0 hanc]
    simp only [Pi.single_apply]
    have hsum : (∑ s_1 : Fin (2 ^ N), if qBit anc s_1.val = 1 then
        (starRingEnd ℂ ((if s_1 = t0 then 1 else 0 : ℂ)) *
          (if s_1 = t0 then 1 else 0 : ℂ)).re else 0) =
        (if qBit anc t0.val = 1 then 1 else 0 : ℝ) := by
      by_cases h : qBit anc t0.val = 1
      · simp only [h, ite_true]
        have hmain : (∑ s_1 : Fin (2 ^ N), if qBit anc s_1.val = 1 then
            (starRingEnd ℂ ((if s_1 = t0 then 1 else 0 : ℂ)) *
              (if s_1 = t0 then 1 else 0 : ℂ)).re else 0) =
            (if qBit anc t0.val = 1 then
              (starRingEnd ℂ ((if t0 = t0 then 1 else 0 : ℂ)) *
                (if t0 = t0 then 1 else 0 : ℂ)).re else 0) := by
          apply Finset.sum_eq_single t0
          · intro b _ hb
            simp [hb]
          · intro hc
            simp at hc
        rw [hmain]
        simp [h]
      · simp only [h, ite_false]
        apply Finset.sum_eq_zero
        intro s_1 _
        by_cases heq : s_1 = t0
        · simp [heq, h]
        · simp [heq]
    exact hsum
  rw [hswap_acc]
  have hpar : (((qBit anc s1.val).val : ZMod 2) =
      (b ⬝ᵥ localBits addr s.val)) := by
    have h0 : ((qBit anc s.val).val : ZMod 2) = 0 := by
      simp [hs]
    have hconv : (b ⬝ᵥ localBits addr s.val) =
        (List.map (fun i => b i * localBits addr s.val i) (List.finRange k)).sum := by
      unfold dotProduct
      rw [Fin.sum_univ_def]
    rw [hpar1, h0, zero_add, hconv]
  have hval : (qBit anc s1.val).val = (b ⬝ᵥ localBits addr s.val).val := by
    have h2 : ((qBit anc s1.val).val : ZMod 2) =
        ((b ⬝ᵥ localBits addr s.val).val : ZMod 2) := by
      rw [hpar]
      simp [ZMod.natCast_val, ZMod.cast_id]
    have hb1 := Fin.is_lt (qBit anc s1.val)
    have hb2 := ZMod.val_lt (b ⬝ᵥ localBits addr s.val)
    have h3 := congrArg ZMod.val h2
    rw [ZMod.val_cast_of_lt hb1, ZMod.val_cast_of_lt hb2] at h3
    exact h3
  by_cases hn : neg = true
  · simp only [hn, ite_true] at ⊢
    have hflip : qBit anc (flipBit N anc s1).val = 1 ↔
        qBit anc s1.val = 0 := by
      have hself := qBit_flipBit_self hanc s1
      rw [hself]
      rcases fin2_dichot (qBit anc s1.val) with h0 | h1
      · simp [h0]
      · simp [h1]
    by_cases h : qBit anc s1.val = 0
    · simp [h, hflip] at ⊢
      have hpow : (-1 : ℝ) ^ (b ⬝ᵥ localBits addr s.val).val = 1 := by
        have : (b ⬝ᵥ localBits addr s.val).val = 0 := by
          have := congrArg Fin.val h
          simp [hval] at this
          omega
        simp [this]
      simp [hpow]
    · simp at ⊢
      have h1 : qBit anc s1.val = 1 := (fin2_dichot _).resolve_left h
      simp [h1, hflip] at ⊢
      have hpow : (-1 : ℝ) ^ (b ⬝ᵥ localBits addr s.val).val = -1 := by
        have : (b ⬝ᵥ localBits addr s.val).val = 1 := by
          have := congrArg Fin.val h1
          simp [hval] at this
          omega
        simp [this]
      simp [hpow]
      norm_num [hpow]
  · simp only [hn] at ⊢
    by_cases h : qBit anc s1.val = 1
    · simp [h] at ⊢
      have hpow : (-1 : ℝ) ^ (b ⬝ᵥ localBits addr s.val).val = -1 := by
        have : (b ⬝ᵥ localBits addr s.val).val = 1 := by
          have := congrArg Fin.val h
          simp [hval] at this
          omega
        simp [this]
      simp [hpow]
    · simp [h] at ⊢
      have h0 : qBit anc s1.val = 0 := (fin2_dichot _).resolve_right h
      simp at ⊢
      have hpow : (-1 : ℝ) ^ (b ⬝ᵥ localBits addr s.val).val = 1 := by
        have : (b ⬝ᵥ localBits addr s.val).val = 0 := by
          have := congrArg Fin.val h0
          simp [hval] at this
          omega
        simp [this]
      simp [hpow]
      norm_num [hpow]
/-- Locality: let every address `addr i` be below `N`, and let the ancilla
satisfy `0 < anc < N` and `addr i ≠ anc` for every `i`. For a qubit `q`
outside the addresses and the ancilla, if the state vanishes at every basis
state whose bit `q` differs from `v`, so does its image under the core. -/
theorem perLabelCore_preserves_qBit {N k anc : ℕ} {addr : Fin k → ℕ}
    (a b : Fin k → ZMod 2) (neg : Bool)
    (hlt : ∀ i, addr i < N) (hanc0 : 0 < anc) (hanc : anc < N)
    (hne : ∀ i, addr i ≠ anc)
    {q : ℕ} (hq : ∀ i, addr i ≠ q) (hqa : q ≠ anc) (v : Fin 2)
    {ψ : Fin (2 ^ N) → ℂ}
    (hψ : ∀ s : Fin (2 ^ N), qBit q s.val ≠ v → ψ s = 0) :
    ∀ s : Fin (2 ^ N), qBit q s.val ≠ v →
      applyCircuit N (perLabelCore addr a b neg anc) ψ s = 0 := by
  intro s hs
  unfold perLabelCore
  rw [applyCircuit_append]
  have hflat_av : ∀ g ∈ (List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc),
      q ≠ g.1 ∧ q ≠ g.2.1 := by
    intro g hg
    simp only [List.mem_flatMap, List.mem_append] at hg
    obtain ⟨i, _, hg⟩ := hg
    rcases hg with hg_basis | hg_parity
    · unfold basisChangeGates at hg_basis
      by_cases ha : a i = 1
      · simp only [ha, ite_true] at hg_basis
        by_cases hbb : b i = 1
        · simp only [hbb, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hg_basis
          rcases hg_basis with rfl | rfl
          · unfold embeddedGate
            by_cases h : addr i < anc
            · rw [ite_eq_left h]
              exact ⟨Ne.symm (hq i), hqa⟩
            · rw [ite_eq_right h]
              exact ⟨hqa, Ne.symm (hq i)⟩
          · unfold embeddedGate
            by_cases h : addr i < anc
            · rw [ite_eq_left h]
              exact ⟨Ne.symm (hq i), hqa⟩
            · rw [ite_eq_right h]
              exact ⟨hqa, Ne.symm (hq i)⟩
        · simp only [hbb, ite_false, List.mem_singleton] at hg_basis
          rcases hg_basis with rfl
          unfold embeddedGate
          by_cases h : addr i < anc
          · rw [ite_eq_left h]
            exact ⟨Ne.symm (hq i), hqa⟩
          · rw [ite_eq_right h]
            exact ⟨hqa, Ne.symm (hq i)⟩
      · simp [ha] at hg_basis
    · unfold parityGates at hg_parity
      by_cases h : a i = 0 ∧ b i = 0
      · simp [h] at hg_parity
      · simp only [h, ite_false, List.mem_singleton] at hg_parity
        rcases hg_parity with rfl
        unfold controlledGate
        by_cases hc : addr i < anc
        · rw [ite_eq_left hc]
          exact ⟨Ne.symm (hq i), hqa⟩
        · rw [ite_eq_right hc]
          exact ⟨hqa, Ne.symm (hq i)⟩
  have hflat_wf : ∀ g ∈ (List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc),
      QGateWellFormed N g := by
    intro g hg
    have hmem : g ∈ perLabelCircuit addr a b neg anc := by
      unfold perLabelCircuit perLabelCore
      simp only [List.mem_append] at hg ⊢
      exact Or.inl (Or.inl hg)
    exact perLabelCircuit_wellFormed a b neg hlt hanc0 hanc hne g hmem
  have hcomb : ∀ g ∈ (List.finRange k).flatMap (fun i =>
      basisChangeGates (a i) (b i) (addr i) anc ++
        parityGates (a i) (b i) (addr i) anc),
      QGateWellFormed N g ∧ q ≠ g.1 ∧ q ≠ g.2.1 := by
    intro g hg
    exact ⟨hflat_wf g hg, hflat_av g hg⟩
  set ψ₁ := applyCircuit N ((List.finRange k).flatMap (fun i =>
    basisChangeGates (a i) (b i) (addr i) anc ++
      parityGates (a i) (b i) (addr i) anc)) ψ with hψ₁def
  have hψ1 : ∀ t : Fin (2 ^ N), qBit q t.val ≠ v → ψ₁ t = 0 := by
    intro t ht
    simp only [hψ₁def]
    exact applyCircuit_eq_zero_of_qBit_ne hcomb v hψ t ht
  by_cases hn : neg = true
  · simp only [hn, ite_true] at ⊢
    simp only [applyCircuit, List.foldl_cons, List.foldl_nil] at ⊢
    by_cases hq0 : q = 0
    · subst hq0
      have h0N : 0 < N := Nat.lt_trans hanc0 hanc
      have hne0 : anc ≠ 0 := by omega
      have hx : applyGate N (embeddedGate xGate anc 0) ψ₁ s = ψ₁ (flipBit N anc s) := by
        apply applyGate_embeddedGate_xGate <;> assumption
      rw [hx]
      have h0ne : (0 : ℕ) ≠ anc := by omega
      have hflip : qBit 0 (flipBit N anc s).val = qBit 0 s.val :=
        qBit_flipBit_of_ne h0ne s
      exact hψ1 _ (hflip ▸ hs)
    · have hang : q ≠ (embeddedGate xGate anc 0).1 ∧
        q ≠ (embeddedGate xGate anc 0).2.1 := by
        unfold embeddedGate
        rw [ite_eq_right (Nat.not_lt_zero anc)]
        exact ⟨hq0, hqa⟩
      have hwf_sign : QGateWellFormed N (embeddedGate xGate anc 0) := by
        have h0N : 0 < N := Nat.lt_trans hanc0 hanc
        have hne0 : anc ≠ 0 := by omega
        exact embeddedGate_wellFormed xGate xGate_unitary hne0 hanc h0N
      have h1 := hang.1
      have h2 := hang.2
      exact applyGate_eq_zero_of_qBit_ne hwf_sign h1 h2 v hψ1 s hs
  · simp only [hn] at ⊢
    simp only [applyCircuit] at ⊢
    exact hψ1 _ hs

end Cslib.Complexity.Classes.QMA
