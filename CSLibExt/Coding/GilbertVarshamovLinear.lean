/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LinearCode
public import MathlibExt.InformationTheory.HammingBall

/-!
# The Gilbert–Varshamov bound for linear codes

Varshamov's greedy argument for linear codes: if a linear code `C` of dimension `k` and minimum
distance at least `d` has `q ^ k · Vol_q(n, d - 1) < q ^ n`, its codewords' balls of radius
`d - 1` miss some word `v`, and `C + F v` still has minimum distance at least `d`, with dimension
`k + 1`. Iterating from the zero code:

* `exists_linearCode_finrank_eq` (**Gilbert–Varshamov bound, linear form**): over a finite field
  with `q` elements, if `q ^ k · Vol_q(n, d - 1) < q ^ n` and `d ≥ 1`, there is a linear code of
  length `n`, dimension `k + 1` and minimum distance at least `d`.

## References

* R. R. Varshamov, "Estimate of the number of signals in error correcting codes", *Doklady
  Akademii Nauk SSSR* 117 (1957), 739–741.
* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Theorem 4.2.1 (the linear-code part, proved there with a random generator matrix in Section
  4.2.2).
-/

@[expose] public section

namespace Cslib.CodingTheory.GilbertVarshamov

open Module Finset LinearCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- **One greedy step.** Let `C` be a linear code of length `n` over a finite field with `q`
elements whose nonzero codewords all have weight at least `d ≥ 1`. If
`q ^ dim C · Vol_q(n, d - 1) < q ^ n`, some word `v` lies at distance at least `d` from every
codeword, and the code `C + F v` has dimension `dim C + 1` and all nonzero weights at least `d`
(Varshamov's argument; Guruswami, Rudra and Sudan, *Essential Coding Theory*, draft of August 26,
2025, Theorem 4.2.1, linear part). -/
theorem exists_extend {C : LinearCode F (Fin n)} {d : ℕ} (hd : 1 ≤ d)
    (hC : ∀ c ∈ C, c ≠ 0 → d ≤ hammingNorm c)
    (hvol : Fintype.card F ^ finrank F C *
      ∑ i ∈ range d, n.choose i * (Fintype.card F - 1) ^ i < Fintype.card F ^ n) :
    ∃ C' : LinearCode F (Fin n), C ≤ C' ∧ finrank F C' = finrank F C + 1 ∧
      ∀ c ∈ C', c ≠ 0 → d ≤ hammingNorm c := by
  classical
  set S : Finset (Fin n → F) := univ.filter (· ∈ C) with hS
  -- Some word is far from every codeword.
  obtain ⟨v, hv⟩ : ∃ v : Fin n → F, ∀ c ∈ C, d ≤ hammingDist v c := by
    by_contra hcon
    push Not at hcon
    have hcover : (univ : Finset (Fin n → F)) ⊆ S.biUnion fun c => Hamming.ball c (d - 1) := by
      intro v _
      obtain ⟨c, hc, hlt⟩ := hcon v
      rw [mem_biUnion]
      refine ⟨c, by simpa [hS] using hc, ?_⟩
      rw [Hamming.mem_ball, hammingDist_comm]
      omega
    have h1 := card_le_card hcover
    have h2 : (S.biUnion fun c => Hamming.ball c (d - 1)).card ≤
        S.card * ∑ i ∈ range d, n.choose i * (Fintype.card F - 1) ^ i := by
      refine card_biUnion_le.trans ?_
      rw [← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun c _ => ?_
      rw [Hamming.card_ball, Fintype.card_fin, Nat.sub_add_cancel hd]
    rw [card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    rw [show S.card = Fintype.card F ^ finrank F C from card_filter_mem C] at h2
    omega
  have hvC : v ∉ C := by
    intro hvC
    have := hv v hvC
    rw [hammingDist_self] at this
    omega
  refine ⟨C ⊔ F ∙ v, le_sup_left, ?_, ?_⟩
  · have hinf : C ⊓ F ∙ v = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxC, hxv⟩ := Submodule.mem_inf.mp hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxv
      by_cases ha : a = 0
      · simp [ha]
      · exact absurd (by simpa [ha] using C.smul_mem a⁻¹ hxC) hvC
    have hv0 : v ≠ 0 := fun h => hvC (h ▸ C.zero_mem)
    have := Submodule.finrank_sup_add_finrank_inf_eq C (F ∙ v)
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at this
    exact this
  · intro x hx hx0
    obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    by_cases ha : a = 0
    · subst ha
      simp only [zero_smul, add_zero] at hx0 ⊢
      exact hC c hc hx0
    · have hmem : -(a⁻¹ • c) ∈ C := C.neg_mem (C.smul_mem _ hc)
      have heq : c + a • v = a • (v - -(a⁻¹ • c)) := by
        rw [sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul, add_comm]
      rw [heq, hammingNorm_smul (fun _ => smul_right_injective F ha),
        ← hammingDist_eq_hammingNorm_sub]
      exact hv _ hmem

/-- **Gilbert–Varshamov bound for linear codes.** Let `F` be a finite field with `q` elements and
let `n, k, d` be natural numbers with `d ≥ 1`. If
`q ^ k · ∑_{i=0}^{d-1} C(n, i) (q - 1) ^ i < q ^ n`, there is a linear code of length `n` over
`F`, of dimension `k + 1`, whose minimum distance is at least `d`.

This is Varshamov's greedy form of the linear part of Theorem 4.2.1 of Guruswami, Rudra and
Sudan, *Essential Coding Theory* (draft of August 26, 2025), where the linear part is proved with
a uniformly random generator matrix instead. Source: R. R. Varshamov, "Estimate of the number of
signals in error correcting codes", *Doklady Akademii Nauk SSSR* 117 (1957), 739–741. -/
theorem exists_linearCode_finrank_eq {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (hvol : Fintype.card F ^ k * ∑ i ∈ range d, n.choose i * (Fintype.card F - 1) ^ i <
      Fintype.card F ^ n) :
    ∃ C : LinearCode F (Fin n), finrank F C = k + 1 ∧ (d : ℕ∞) ≤ C.minDist := by
  suffices h : ∀ j ≤ k, ∃ C : LinearCode F (Fin n), finrank F C = j + 1 ∧
      ∀ c ∈ C, c ≠ 0 → d ≤ hammingNorm c by
    obtain ⟨C, hdim, hw⟩ := h k le_rfl
    refine ⟨C, hdim, ?_⟩
    rw [minDist_eq_minWeight, le_minWeight_iff]
    exact fun c hc hne => by exact_mod_cast hw c hc hne
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos (α := F)
  intro j
  induction j with
  | zero =>
    intro hj
    have h0 : Fintype.card F ^ (0 : ℕ) * ∑ i ∈ range d, n.choose i * (Fintype.card F - 1) ^ i <
        Fintype.card F ^ n :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq (Nat.zero_le k))) hvol
    obtain ⟨C, -, hdim, hw⟩ :=
      exists_extend (C := ⊥) hd (by simp) (by rwa [finrank_bot F (Fin n → F)])
    exact ⟨C, by rw [hdim, finrank_bot F (Fin n → F)], hw⟩
  | succ j ih =>
    intro hj
    obtain ⟨C, hdim, hw⟩ := ih (by omega)
    have hstep : Fintype.card F ^ finrank F C *
        ∑ i ∈ range d, n.choose i * (Fintype.card F - 1) ^ i < Fintype.card F ^ n := by
      rw [hdim]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hj)) hvol
    obtain ⟨C', -, hdim', hw'⟩ := exists_extend hd hw hstep
    exact ⟨C', by rw [hdim', hdim], hw'⟩

end Cslib.CodingTheory.GilbertVarshamov
