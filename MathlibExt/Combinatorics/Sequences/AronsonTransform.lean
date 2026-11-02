/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MetaMathlibExt

private noncomputable def aronsonChoose (n₀ : ℕ) (β : ℕ → ℕ) (l : List ℕ) : ℕ :=
  if _ : l = [] then
    sInf {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)}
  else
    let i := l.length - 1
    let n := n₀ + i + 1
    let c := l.getLastD n₀
    let Q : Prop := ∃ j, j ≤ i ∧ l[j]? = some n
    sInf {m | c < m ∧ (((Q ∨ m = n) ↔ m ∈ Set.range β))}

private noncomputable def aronsonHist (n₀ : ℕ) (β : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | (k + 1) => (aronsonHist n₀ β k) ++ [aronsonChoose n₀ β (aronsonHist n₀ β k)]

private noncomputable def aronsonSeq (n₀ : ℕ) (β : ℕ → ℕ) (k : ℕ) : ℕ :=
  aronsonChoose n₀ β (aronsonHist n₀ β k)

private lemma aronson_A0_nonempty (n₀ : ℕ) (β : ℕ → ℕ)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)}.Nonempty := by
  classical
  by_cases hn₀ : n₀ ∈ Set.range β
  · exact ⟨n₀, le_refl n₀, by simp [hn₀]⟩
  · obtain ⟨m, hm_mem, hm_gt⟩ := hβ_complement.exists_gt n₀
    simp only [Set.mem_ofPred_eq] at hm_mem
    obtain ⟨hm_le, hm_not⟩ := hm_mem
    refine ⟨m, hm_le, ?_⟩
    have hm_ne : m ≠ n₀ := ne_of_gt hm_gt
    simp [hm_ne, hm_not]

private lemma aronson_step_nonempty (n₀ : ℕ) (β : ℕ → ℕ) (l : List ℕ)
    (hβ_strictMono : StrictMono β)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    {m : ℕ | l.getLastD n₀ < m ∧
      ((((∃ j, j ≤ l.length - 1 ∧ l[j]? = some (n₀ + (l.length - 1) + 1)) ∨
        m = (n₀ + (l.length - 1) + 1)) ↔
        m ∈ Set.range β))}.Nonempty := by
  classical
  set i := l.length - 1 with hi
  set n := n₀ + i + 1 with hn
  set c := l.getLastD n₀ with hc
  by_cases hQ : (∃ j, j ≤ i ∧ l[j]? = some n)
  · refine ⟨β (c + 1), ?_, ?_⟩
    · have hle : c + 1 ≤ β (c + 1) := hβ_strictMono.le_apply
      omega
    · simp only [hQ, true_or, true_iff]
      exact ⟨_, rfl⟩
  · obtain ⟨m, hm_mem, hm_gt⟩ := hβ_complement.exists_gt (max c n)
    simp only [Set.mem_ofPred_eq] at hm_mem
    obtain ⟨hm_le, hm_not⟩ := hm_mem
    have hmc : c < m := lt_of_le_of_lt (le_max_left c n) hm_gt
    have hmn : m ≠ n := ne_of_gt (lt_of_le_of_lt (le_max_right c n) hm_gt)
    refine ⟨m, hmc, ?_⟩
    simp [hQ, hmn, hm_not]

private lemma aronsonHist_length (n₀ : ℕ) (β : ℕ → ℕ) (k : ℕ) :
    (aronsonHist n₀ β k).length = k := by
  induction k with
  | zero => rfl
  | succ n ih => simp [aronsonHist, ih]

private lemma aronsonHist_get (n₀ : ℕ) (β : ℕ → ℕ) (k : ℕ) :
    ∀ j, j < k → (aronsonHist n₀ β k)[j]? = some (aronsonSeq n₀ β j) := by
  induction k with
  | zero =>
    intro j hj
    omega
  | succ n ih =>
    intro j hj
    have hlen : (aronsonHist n₀ β n).length = n := aronsonHist_length n₀ β n
    have heq : aronsonHist n₀ β (n + 1) = aronsonHist n₀ β n ++ [aronsonSeq n₀ β n] := rfl
    by_cases hjk : j < n
    · have h1 : (aronsonHist n₀ β n ++ [aronsonSeq n₀ β n])[j]? =
          (aronsonHist n₀ β n)[j]? :=
          List.getElem?_append_left (by omega)
      rw [heq, h1]
      exact ih j hjk
    · have hjk_eq : j = n := by omega
      rw [hjk_eq]
      have h2 : (aronsonHist n₀ β n ++ [aronsonSeq n₀ β n])[n]? =
          ([aronsonSeq n₀ β n] : List ℕ)[n - (aronsonHist n₀ β n).length]? :=
        List.getElem?_append_right (by omega)
      rw [heq, h2, hlen]
      simp

private lemma aronsonHist_lastD (n₀ : ℕ) (β : ℕ → ℕ) (k : ℕ) :
    (aronsonHist n₀ β (k + 1)).getLastD n₀ = aronsonSeq n₀ β k := by
  have heq : aronsonHist n₀ β (k + 1) = aronsonHist n₀ β k ++ [aronsonSeq n₀ β k] := rfl
  rw [heq]
  exact List.getLastD_concat

private lemma aronsonChoose_nil (n₀ : ℕ) (β : ℕ → ℕ) :
    aronsonChoose n₀ β [] = sInf {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)} := by
  unfold aronsonChoose
  rw [dite_eq_left rfl]

private lemma aronsonChoose_ne (n₀ : ℕ) (β : ℕ → ℕ) (l : List ℕ) (hl : l ≠ []) :
    aronsonChoose n₀ β l =
      sInf {m : ℕ | l.getLastD n₀ < m ∧
        ((((∃ j, j ≤ l.length - 1 ∧ l[j]? = some (n₀ + (l.length - 1) + 1)) ∨
          m = (n₀ + (l.length - 1) + 1)) ↔
          m ∈ Set.range β))} := by
  unfold aronsonChoose
  rw [dite_eq_right hl]

private lemma aronsonSeq_zero_eq (n₀ : ℕ) (β : ℕ → ℕ) :
    aronsonSeq n₀ β 0 = sInf {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)} := by
  have h : aronsonHist n₀ β 0 = [] := rfl
  simp [aronsonSeq, h, aronsonChoose_nil]

private lemma aronsonHist_Q_iff (n₀ : ℕ) (β : ℕ → ℕ) (i : ℕ) :
    (∃ j, j ≤ i ∧ (aronsonHist n₀ β (i + 1))[j]? = some (n₀ + i + 1)) ↔
    (∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) := by
  constructor
  · rintro ⟨j, hj, hmem⟩
    have h := aronsonHist_get n₀ β (i + 1) j (by omega)
    rw [hmem] at h
    exact ⟨j, hj, Option.some_inj.mp h.symm⟩
  · rintro ⟨j, hj, heq⟩
    have h := aronsonHist_get n₀ β (i + 1) j (by omega)
    exact ⟨j, hj, by rw [h, heq]⟩

private lemma aronsonSeq_succ_mem (n₀ : ℕ) (β : ℕ → ℕ) (i : ℕ)
    (hβ_strictMono : StrictMono β)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    aronsonSeq n₀ β (i + 1) ∈
      {m | aronsonSeq n₀ β i < m ∧
        ((((∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) ∨ m = n₀ + i + 1) ↔
          m ∈ Set.range β))} := by
  have hlen : (aronsonHist n₀ β (i + 1)).length = i + 1 := aronsonHist_length n₀ β (i + 1)
  have hne_hist : aronsonHist n₀ β (i + 1) ≠ [] := by
    intro hcon
    rw [hcon] at hlen
    simp at hlen
  have hchoose := aronsonChoose_ne n₀ β (aronsonHist n₀ β (i + 1)) hne_hist
  have hnonempty :=
    aronson_step_nonempty n₀ β (aronsonHist n₀ β (i + 1)) hβ_strictMono hβ_complement
  have hmem0 : sInf {m : ℕ | (aronsonHist n₀ β (i + 1)).getLastD n₀ < m ∧
      ((((∃ j, j ≤ (aronsonHist n₀ β (i + 1)).length - 1 ∧
        (aronsonHist n₀ β (i + 1))[j]? = some (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ∨
        m = (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ↔ m ∈ Set.range β))} ∈
      {m : ℕ | (aronsonHist n₀ β (i + 1)).getLastD n₀ < m ∧
      ((((∃ j, j ≤ (aronsonHist n₀ β (i + 1)).length - 1 ∧
        (aronsonHist n₀ β (i + 1))[j]? = some (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ∨
        m = (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ↔ m ∈ Set.range β))} :=
    Nat.sInf_mem hnonempty
  have hQ := aronsonHist_Q_iff n₀ β i
  have hbound := aronsonHist_lastD n₀ β i
  have hlen_sub : (aronsonHist n₀ β (i + 1)).length - 1 = i := by
    rw [hlen, Nat.add_sub_cancel]
  have hset_eq : {m : ℕ | (aronsonHist n₀ β (i + 1)).getLastD n₀ < m ∧
      ((((∃ j, j ≤ (aronsonHist n₀ β (i + 1)).length - 1 ∧
        (aronsonHist n₀ β (i + 1))[j]? = some (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ∨
        m = (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ↔ m ∈ Set.range β))} =
      {m | aronsonSeq n₀ β i < m ∧
        ((((∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) ∨ m = n₀ + i + 1) ↔
          m ∈ Set.range β))} := by
    ext m
    simp only [Set.mem_ofPred_eq]
    rw [hbound, hlen_sub, hQ]
  rw [hset_eq] at hmem0
  have hseq : aronsonSeq n₀ β (i + 1) =
      sInf {m | aronsonSeq n₀ β i < m ∧
        ((((∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) ∨ m = n₀ + i + 1) ↔
          m ∈ Set.range β))} := by
    change aronsonChoose n₀ β (aronsonHist n₀ β (i + 1)) = _
    rw [hchoose, hset_eq]
  rw [hseq]
  exact hmem0



private lemma aronsonSeq_zero_mem (n₀ : ℕ) (β : ℕ → ℕ)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    aronsonSeq n₀ β 0 ∈ {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)} := by
  rw [aronsonSeq_zero_eq]
  exact Nat.sInf_mem (aronson_A0_nonempty n₀ β hβ_complement)

private lemma aronsonSeq_zero_le (n₀ : ℕ) (β : ℕ → ℕ)
    (m : ℕ) (hm1 : n₀ ≤ m) (hm2 : (m = n₀) ↔ m ∈ Set.range β) :
    aronsonSeq n₀ β 0 ≤ m := by
  have h : sInf {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)} ≤ m :=
    Nat.sInf_le ⟨hm1, hm2⟩
  rwa [← aronsonSeq_zero_eq n₀ β] at h

private lemma aronsonSeq_succ_le (n₀ : ℕ) (β : ℕ → ℕ) (i m : ℕ)
    (hm1 : aronsonSeq n₀ β i < m)
    (hm2 : ((((∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) ∨ m = n₀ + i + 1) ↔
      m ∈ Set.range β))) :
    aronsonSeq n₀ β (i + 1) ≤ m := by
  have hlen : (aronsonHist n₀ β (i + 1)).length = i + 1 := aronsonHist_length n₀ β (i + 1)
  have hne_hist : aronsonHist n₀ β (i + 1) ≠ [] := by
    intro hcon
    rw [hcon] at hlen
    simp at hlen
  have hchoose := aronsonChoose_ne n₀ β (aronsonHist n₀ β (i + 1)) hne_hist
  have hQ := aronsonHist_Q_iff n₀ β i
  have hbound := aronsonHist_lastD n₀ β i
  have hlen_sub : (aronsonHist n₀ β (i + 1)).length - 1 = i := by
    rw [hlen, Nat.add_sub_cancel]
  have hm_old : m ∈ {m : ℕ | (aronsonHist n₀ β (i + 1)).getLastD n₀ < m ∧
      ((((∃ j, j ≤ (aronsonHist n₀ β (i + 1)).length - 1 ∧
        (aronsonHist n₀ β (i + 1))[j]? = some (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ∨
        m = (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ↔ m ∈ Set.range β))} := by
    refine ⟨?_, ?_⟩
    · rw [hbound]
      exact hm1
    · rw [hlen_sub, hQ]
      exact hm2
  have hle := Nat.sInf_le hm_old
  have heq : aronsonSeq n₀ β (i + 1) =
      sInf {m : ℕ | (aronsonHist n₀ β (i + 1)).getLastD n₀ < m ∧
        ((((∃ j, j ≤ (aronsonHist n₀ β (i + 1)).length - 1 ∧
          (aronsonHist n₀ β (i + 1))[j]? =
            some (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ∨
          m = (n₀ + ((aronsonHist n₀ β (i + 1)).length - 1) + 1)) ↔ m ∈ Set.range β))} := by
    change aronsonChoose n₀ β (aronsonHist n₀ β (i + 1)) = _
    exact hchoose
  rw [heq]
  exact hle


/-! # Existence and uniqueness of the Aronson transform
-/

/-- **Existence and uniqueness of the Aronson transform, general form.** Let $n_0$ be a natural
number and let $\beta : \mathbb{N} \to \mathbb{N}$ be strictly increasing such that infinitely
many integers $m \ge n_0$ are not values of $\beta$. Then there is exactly one sequence
$\alpha : \mathbb{N} \to \mathbb{N}$ such that $\alpha$ is strictly increasing, $\alpha_i \ge n_0$
for every $i$, $\alpha_0$ is the least integer $m \ge n_0$ such that $m = n_0$ holds exactly when
$m$ is a value of $\beta$, and, for every $i \ge 0$, $\alpha_{i+1}$ is the least integer
$m > \alpha_i$ such that $n_0 + i + 1 \in \{\alpha_0, \dots, \alpha_i, m\}$ holds exactly when $m$
is a value of $\beta$.

The values of $\beta$ are not required to be at least $n_0$. -/
theorem aronsonTransform_existsUnique_general
    (n₀ : ℕ)
    (β : ℕ → ℕ)
    (hβ_strictMono : StrictMono β)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    ∃! α : ℕ → ℕ,
      StrictMono α ∧
      (∀ i, n₀ ≤ α i) ∧
      (((α 0 = n₀) ↔ α 0 ∈ Set.range β) ∧
        ∀ m, n₀ ≤ m →
          ((m = n₀) ↔ m ∈ Set.range β) →
          α 0 ≤ m) ∧
      ∀ i,
        let n := n₀ + i + 1
        ((((∃ j, j ≤ i ∧ α j = n) ∨ α (i + 1) = n) ↔
            α (i + 1) ∈ Set.range β) ∧
          ∀ m, α i < m →
            (((∃ j, j ≤ i ∧ α j = n) ∨ m = n) ↔ m ∈ Set.range β) →
            α (i + 1) ≤ m) := by
  refine ⟨aronsonSeq n₀ β, ?_, ?_⟩
  · -- Existence: the greedy sequence satisfies all clauses.
    have hmono : StrictMono (aronsonSeq n₀ β) := by
      apply strictMono_nat_of_lt_succ
      intro n
      obtain ⟨hlt, _⟩ := aronsonSeq_succ_mem n₀ β n hβ_strictMono hβ_complement
      exact hlt
    have h0mem := aronsonSeq_zero_mem n₀ β hβ_complement
    obtain ⟨h0le, h0iff⟩ := h0mem
    refine ⟨hmono, ?_, ?_, ?_⟩
    · intro i
      exact le_trans h0le (hmono.monotone (Nat.zero_le i))
    · refine ⟨h0iff, ?_⟩
      intro m hm1 hm2
      exact aronsonSeq_zero_le n₀ β m hm1 hm2
    · intro i
      obtain ⟨_, hiff⟩ := aronsonSeq_succ_mem n₀ β i hβ_strictMono hβ_complement
      refine ⟨hiff, ?_⟩
      intro m hm1 hm2
      exact aronsonSeq_succ_le n₀ β i m hm1 hm2
  · -- Uniqueness: any sequence satisfying the clauses equals the greedy one.
    intro y hy
    obtain ⟨hyMono, hyLower, hyZero, hySucc⟩ := hy
    obtain ⟨hy0iff, hy0min⟩ := hyZero
    have hbase : y 0 = aronsonSeq n₀ β 0 := by
      obtain ⟨h0le, h0iff⟩ := aronsonSeq_zero_mem n₀ β hβ_complement
      apply le_antisymm
      · exact hy0min _ h0le h0iff
      · exact aronsonSeq_zero_le n₀ β _ (hyLower 0) hy0iff
    have hstep : ∀ i, (∀ j, j ≤ i → y j = aronsonSeq n₀ β j) →
        y (i + 1) = aronsonSeq n₀ β (i + 1) := by
      intro i ih
      have hQeq : (∃ j, j ≤ i ∧ y j = n₀ + i + 1) ↔
          (∃ j, j ≤ i ∧ aronsonSeq n₀ β j = n₀ + i + 1) := by
        constructor
        · rintro ⟨j, hj, hje⟩
          exact ⟨j, hj, by rw [← ih j hj]; exact hje⟩
        · rintro ⟨j, hj, hje⟩
          exact ⟨j, hj, by rw [ih j hj]; exact hje⟩
      have hyi := hySucc i
      obtain ⟨hy_iff, hy_min⟩ := hyi
      obtain ⟨hlt, hiff⟩ := aronsonSeq_succ_mem n₀ β i hβ_strictMono hβ_complement
      apply le_antisymm
      · apply hy_min
        · rw [ih i (le_refl i)]
          exact hlt
        · rw [hQeq]
          exact hiff
      · apply aronsonSeq_succ_le
        · rw [← ih i (le_refl i)]
          exact hyMono (Nat.lt_succ_self i)
        · rw [← hQeq]
          exact hy_iff
    have hall : ∀ i j, j ≤ i → y j = aronsonSeq n₀ β j := by
      intro i
      induction i with
      | zero =>
        intro j hj
        have hjeq : j = 0 := by omega
        rw [hjeq]
        exact hbase
      | succ n ih =>
        intro j hj
        by_cases hjn : j ≤ n
        · exact ih j hjn
        · have hjeq : j = n + 1 := by omega
          rw [hjeq]
          exact hstep n (fun k hk => ih k hk)
    exact funext fun i => hall i i (le_refl i)


set_option linter.unusedVariables false in
/--
**Existence and uniqueness of the Aronson transform.** Let $n_0$ be a natural number and let
$\beta : \mathbb{N} \to \mathbb{N}$ be strictly increasing with $\beta_i \ge n_0$ for every $i$,
such that infinitely many integers $m \ge n_0$ are not values of $\beta$. Then there is exactly
one sequence $\alpha : \mathbb{N} \to \mathbb{N}$ such that $\alpha$ is strictly increasing,
$\alpha_i \ge n_0$ for every $i$, $\alpha_0$ is the least integer $m \ge n_0$ such that $m = n_0$
holds exactly when $m$ is a value of $\beta$, and, for every $i \ge 0$, $\alpha_{i+1}$ is the
least integer $m > \alpha_i$ such that $n_0 + i + 1 \in \{\alpha_0, \dots, \alpha_i, m\}$ holds
exactly when $m$ is a value of $\beta$.

The hypothesis $\beta_i \ge n_0$ is not used in the proof.

Source: Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast,
"Numerical Analogues of Aronson's Sequence," Journal of Integer Sequences 6
(2003), Article 03.2.2, Theorem `ThAT1`, lines 782–784 (transform defined
lines 761–780),
https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex

Proves `Wanted` entry `aronsonTransform_existsUnique`.
-/
@[nolint unusedArguments]
theorem aronsonTransform_existsUnique
    (n₀ : ℕ)
    (β : ℕ → ℕ)
    (hβ_strictMono : StrictMono β)
    (hβ_lower : ∀ i, n₀ ≤ β i)
    (hβ_complement : Set.Infinite {m : ℕ | n₀ ≤ m ∧ m ∉ Set.range β}) :
    ∃! α : ℕ → ℕ,
      StrictMono α ∧
      (∀ i, n₀ ≤ α i) ∧
      (((α 0 = n₀) ↔ α 0 ∈ Set.range β) ∧
        ∀ m, n₀ ≤ m →
          ((m = n₀) ↔ m ∈ Set.range β) →
          α 0 ≤ m) ∧
      ∀ i,
        let n := n₀ + i + 1
        ((((∃ j, j ≤ i ∧ α j = n) ∨ α (i + 1) = n) ↔
            α (i + 1) ∈ Set.range β) ∧
          ∀ m, α i < m →
            (((∃ j, j ≤ i ∧ α j = n) ∨ m = n) ↔ m ∈ Set.range β) →
            α (i + 1) ≤ m) := by
  exact aronsonTransform_existsUnique_general n₀ β hβ_strictMono hβ_complement

end MetaMathlibExt
