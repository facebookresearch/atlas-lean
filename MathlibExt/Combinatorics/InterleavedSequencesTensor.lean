/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Interleaved sequences and tensor products of ultrafilters

For ultrafilters `U`, `V` on `ℕ`, a set `X ⊆ ℕ × ℕ` belongs to the tensor product `U ⊗ V` when
`{n | {m | (n, m) ∈ X} ∈ V} ∈ U`. The theorem below, from the paper of Di Nasso and Jin cited in
its docstring, says that `X` lies in both `V₁ ⊗ V₂` and `V₂ ⊗ V₁` for some non-principal
ultrafilters `V₁`, `V₂` on `ℕ` exactly when there are strictly increasing sequences `a`, `b` with
disjoint ranges such that `X` contains the pairs `(a i, b j)` for `i ≤ j` and `(b j, a i)` for
`j < i`.

## Main statements

* `MetaMathlibExt.exists_interleaved_sequences_iff_mem_tensor`: the characterization above.

## Proof

Given the sequences, push the non-principal ultrafilter `hyperfilter ℕ` forward along `a` and
along `b`. The section `{m | (a i, m) ∈ X}` contains `b j` for every `j ≥ i`, and the section at
`b j` contains `a i` for every `i > j`, so all these sections are large and both tensor products
contain `X`. Conversely, we choose the pairs `(a k, b k)` one after the other with
`exists_seq_of_forall_finset_exists`. The point `a k` lies in the `V₁`-large set of the `n` whose
section belongs to `V₂`, in the sections at the earlier points `b j` and above them; then `b k`
lies in the `V₂`-large set of the `n` whose section belongs to `V₁`, in the sections at
`a 0, …, a k` and above `a k`. Hence `a 0 < b 0 < a 1 < b 1 < ⋯`, so both sequences are strictly
increasing and their ranges are disjoint.
-/

open Filter

namespace MetaMathlibExt

/-- **Interleaved sequences and tensor products of ultrafilters.** For ultrafilters $U$, $V$ on
$\mathbb{N} = \{0, 1, 2, \dots\}$ and $X \subseteq \mathbb{N} \times \mathbb{N}$, write
$X \in U \otimes V$ when $\{n : \{m : (n, m) \in X\} \in V\} \in U$. For every
$X \subseteq \mathbb{N} \times \mathbb{N}$ the following are equivalent: (1) there are strictly
increasing sequences $(a_i)_{i \in \mathbb{N}}$, $(b_j)_{j \in \mathbb{N}}$ in $\mathbb{N}$ with
disjoint ranges such that $(a_i, b_j) \in X$ whenever $i \le j$ and $(b_j, a_i) \in X$ whenever
$j < i$; (2) there are non-principal ultrafilters $V_1$, $V_2$ on $\mathbb{N}$ with
$X \in V_1 \otimes V_2$ and $X \in V_2 \otimes V_1$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Lemma 2.1 (`integers-2025-A105-lem-2-1`). -/
public theorem exists_interleaved_sequences_iff_mem_tensor (X : Set (ℕ × ℕ)) :
    (∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧ Disjoint (Set.range a) (Set.range b) ∧
        (∀ i j, i ≤ j → (a i, b j) ∈ X) ∧ (∀ i j, j < i → (b j, a i) ∈ X)) ↔
      ∃ V₁ V₂ : Ultrafilter ℕ, (V₁ : Filter ℕ) ≤ cofinite ∧ (V₂ : Filter ℕ) ≤ cofinite ∧
        {n | {m | (n, m) ∈ X} ∈ V₂} ∈ V₁ ∧ {n | {m | (n, m) ∈ X} ∈ V₁} ∈ V₂ := by
  constructor
  · -- The images of `hyperfilter ℕ` under `a` and `b` are non-principal, and the section of `X`
    -- at each point of either sequence contains a final segment of the other sequence.
    rintro ⟨a, b, ha, hb, -, hab, hba⟩
    have hle {f : ℕ → ℕ} (hf : StrictMono f) :
        ((hyperfilter ℕ).map f : Filter ℕ) ≤ cofinite := by
      rw [Ultrafilter.coe_map]
      exact (map_mono hyperfilter_le_cofinite).trans hf.injective.tendsto_cofinite
    have hfinal (k : ℕ) {S : Set ℕ} (hS : Set.Ici k ⊆ S) : S ∈ hyperfilter ℕ :=
      hyperfilter_le_cofinite <| mem_of_superset (Nat.cofinite_eq_atTop ▸ Ici_mem_atTop k) hS
    refine ⟨(hyperfilter ℕ).map a, (hyperfilter ℕ).map b, hle ha, hle hb, ?_, ?_⟩
    · exact Ultrafilter.mem_map.2 <| univ_mem' fun i =>
        Ultrafilter.mem_map.2 <| hfinal i fun j hij => hab i j hij
    · exact Ultrafilter.mem_map.2 <| univ_mem' fun j =>
        Ultrafilter.mem_map.2 <| hfinal (j + 1) fun i hji => hba i j hji
  · -- Choose the pairs `(a k, b k)` greedily, each `a k` above every earlier `b j` and each
    -- `b k` above `a k`.
    rintro ⟨V₁, V₂, hV₁, hV₂, h₁₂, h₂₁⟩
    have hIoi {V : Ultrafilter ℕ} (hV : (V : Filter ℕ) ≤ cofinite) (x : ℕ) :
        ∀ᶠ y in (V : Filter ℕ), x < y :=
      hV (Nat.cofinite_eq_atTop ▸ Ioi_mem_atTop x)
    obtain ⟨f, hfP, hfr⟩ := exists_seq_of_forall_finset_exists
      (fun p : ℕ × ℕ => {m | (p.1, m) ∈ X} ∈ V₂ ∧ {m | (p.2, m) ∈ X} ∈ V₁ ∧ (p.1, p.2) ∈ X ∧
        p.1 < p.2)
      (fun p q => p.2 < q.1 ∧ (p.1, q.2) ∈ X ∧ (p.2, q.1) ∈ X) fun s hs => by
        have h₁ : ∀ᶠ y in (V₁ : Filter ℕ),
            {m | (y, m) ∈ X} ∈ V₂ ∧ ∀ x ∈ s, x.2 < y ∧ (x.2, y) ∈ X :=
          Eventually.and h₁₂ <| (eventually_all_finset s).2 fun x hx =>
            (hIoi hV₁ x.2).and (hs x hx).2.1
        obtain ⟨y₁, hy₁, hy₁s⟩ := h₁.exists
        have h₂ : ∀ᶠ y in (V₂ : Filter ℕ),
            {m | (y, m) ∈ X} ∈ V₁ ∧ (y₁, y) ∈ X ∧ y₁ < y ∧ ∀ x ∈ s, (x.1, y) ∈ X :=
          Eventually.and h₂₁ <| Eventually.and hy₁ <| (hIoi hV₂ y₁).and <|
            (eventually_all_finset s).2 fun x hx => (hs x hx).1
        obtain ⟨y₂, hy₂, hy₁₂, hlt, hy₂s⟩ := h₂.exists
        exact ⟨(y₁, y₂), ⟨hy₁, hy₂, hy₁₂, hlt⟩, fun x hx =>
          ⟨(hy₁s x hx).1, hy₂s x hx, (hy₁s x hx).2⟩⟩
    have ha : StrictMono fun i => (f i).1 := fun m n hmn => (hfP m).2.2.2.trans (hfr m n hmn).1
    have hb : StrictMono fun i => (f i).2 := fun m n hmn => (hfr m n hmn).1.trans (hfP n).2.2.2
    refine ⟨fun i => (f i).1, fun i => (f i).2, ha, hb, ?_, fun i j hij => ?_,
      fun i j hji => (hfr j i hji).2.2⟩
    · refine Set.disjoint_left.2 ?_
      rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
      rcases lt_or_ge j i with hji | hij
      · exact (hfr j i hji).1.ne hj
      · exact ((hfP i).2.2.2.trans_le (hb.monotone hij)).ne' hj
    · rcases hij.lt_or_eq with hij | rfl
      · exact (hfr i j hij).2.1
      · exact (hfP i).2.2.1

end MetaMathlibExt
