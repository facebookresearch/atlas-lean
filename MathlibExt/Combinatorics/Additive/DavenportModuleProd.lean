/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Weighted Davenport constant of a product of modules

Embedding zero-sum-free sequences along the two coordinate axes gives the lower bound
`davenport_prod_ge` for the weighted Davenport constant of a product. With separate scalar rings,
`davenport_prod_ring_ge` gives the bound for the product weight set.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence; `D_A(M)` is its least element. -/
local notation "davenportSet(" R ", " M ", " A ")" => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → R, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i • x i = 0}

namespace davenport_prod_ge

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {A : Set R}
  {ι κ : Type*}

private def HasZeroSum (A : Set R) (x : ι → M) : Prop :=
  ∃ I : Finset ι, I.Nonempty ∧ ∃ a : ι → R, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i • x i = 0

private theorem exists_free_pred {d : ℕ} (h : IsLeast (davenportSet(R, M, A)) d) :
    ∃ x : Fin (d - 1) → M, ¬ HasZeroSum A x := by
  by_contra! hall
  obtain ⟨_, ⟨i, _⟩, _⟩ := hall (fun _ => 0)
  have hle := h.2 (show d - 1 ∈ davenportSet(R, M, A) from ⟨i.pos, hall⟩)
  have hd : 0 < d := h.1.1
  omega

private theorem hasZeroSum_of_comp_embedding (e : ι ↪ κ) {x : κ → M} (h : HasZeroSum A (x ∘ e)) :
    HasZeroSum A x := by
  obtain ⟨I, hI, a, ha, hsum⟩ := h
  refine ⟨I.map e, Finset.map_nonempty.mpr hI, Function.extend e a (fun _ => 0), ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simpa [e.injective.extend_apply] using ha i hi
  · simpa [Finset.sum_map, e.injective.extend_apply] using hsum

end davenport_prod_ge

open davenport_prod_ge

/-- **Weighted Davenport constant of a product of modules.** Let $R$ be a ring and
$A \subseteq R$. For an $R$-module $P$, let $D_A(P)$ be the least positive integer $k$, if one
exists, such that every sequence $x_1, \dots, x_k$ in $P$ has a nonempty set of indices $I$ and
weights $a_i \in A$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$. If $M$ and $N$ are
$R$-modules for which $D_A(M)$, $D_A(N)$ and $D_A(M \times N)$ all exist, then
$D_A(M \times N) \ge D_A(M) + D_A(N) - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.2 (`integers-2024-A38-thm-2-2`). -/
public theorem davenport_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Set R) {dM dN d : ℕ}
    (hM : IsLeast (davenportSet(R, M, A)) dM) (hN : IsLeast (davenportSet(R, N, A)) dN)
    (h : IsLeast (davenportSet(R, M × N, A)) d) :
    dM + dN - 1 ≤ d := by
  obtain ⟨x, hx⟩ := exists_free_pred hM
  obtain ⟨y, hy⟩ := exists_free_pred hN
  by_contra! hlt
  have hdM : 0 < dM := hM.1.1
  have hdN : 0 < dN := hN.1.1
  -- A shorter product sequence fits inside the two zero-sum-free blocks.
  let e : Fin d ↪ Fin (dM - 1) ⊕ Fin (dN - 1) :=
    (Fin.castLEEmb (by omega : d ≤ (dM - 1) + (dN - 1))).trans finSumFinEquiv.symm.toEmbedding
  let z : Fin (dM - 1) ⊕ Fin (dN - 1) → M × N :=
    Sum.elim (fun i => (x i, 0)) (fun j => (0, y j))
  obtain ⟨I, ⟨i, hi⟩, a, ha, hsum⟩ :=
    hasZeroSum_of_comp_embedding e (x := z) (h.1.2 (z ∘ e))
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at hsum
  cases i with
  | inl i =>
    apply hx
    refine ⟨I.toLeft, ⟨i, Finset.mem_toLeft.mpr hi⟩, a ∘ Sum.inl,
      fun j hj => ha _ (Finset.mem_toLeft.mp hj), ?_⟩
    simpa [z, Prod.fst_sum] using congrArg Prod.fst hsum
  | inr i =>
    apply hy
    refine ⟨I.toRight, ⟨i, Finset.mem_toRight.mpr hi⟩, a ∘ Sum.inr,
      fun j hj => ha _ (Finset.mem_toRight.mp hj), ?_⟩
    simpa [z, Prod.snd_sum] using congrArg Prod.snd hsum

namespace davenport_prod_ring_ge

/-- Restricting scalars along `f` has the same effect as taking the image of the weight set. -/
private theorem davenportSet_compHom {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M]
    [Module R M] (f : S →+* R) (C : Set S) :
    letI := Module.compHom M f
    davenportSet(S, M, C) = davenportSet(R, M, f '' C) := by
  let := Module.compHom M f
  ext k
  refine and_congr_right fun _ => forall_congr' fun x => ?_
  constructor
  · rintro ⟨I, hI, a, ha, hsum⟩
    exact ⟨I, hI, f ∘ a, fun i hi => Set.mem_image_of_mem f (ha i hi), hsum⟩
  · rintro ⟨I, hI, a, ha, hsum⟩
    choose! b hb heq using ha
    refine ⟨I, hI, b, hb, (Finset.sum_congr rfl fun i hi => ?_).trans hsum⟩
    exact congrArg (· • x i) (heq i hi)

end davenport_prod_ring_ge

/-- **Weighted Davenport constant of a product with product weights.** Let $R$ and $R'$ be rings,
$M$ an $R$-module, $N$ an $R'$-module, $A \subseteq R$ and $B \subseteq R'$. Let $D_A(M)$ be the
least positive integer $k$, if one exists, such that every sequence $x_1, \dots, x_k$ in $M$ has
a nonempty set of indices $I$ and weights $a_i \in A$ for $i \in I$ with
$\sum_{i \in I} a_i x_i = 0$, and define $D_B(N)$ in the same way. Let $D_{A \times B}(M \times N)$
be the least positive integer $k$, if one exists, such that every sequence
$(y_1, z_1), \dots, (y_k, z_k)$ in $M \times N$ has a nonempty set of indices $I$ and weights
$(a_i, b_i) \in A \times B$ for $i \in I$ with $\sum_{i \in I} (a_i y_i, b_i z_i) = 0$. If all
three constants exist, then $D_{A \times B}(M \times N) \ge D_A(M) + D_B(N) - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.1 (`integers-2024-A38-thm-2-1`). -/
public theorem davenport_prod_ring_ge {R R' M N : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (A : Set R) (B : Set R')
    {dA dB d : ℕ} (hA : IsLeast (davenportSet(R, M, A)) dA)
    (hB : IsLeast (davenportSet(R', N, B)) dB)
    (h : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → M × N, ∃ I : Finset (Fin k), I.Nonempty ∧
      ∃ a : Fin k → R × R', (∀ i ∈ I, a i ∈ A ×ˢ B) ∧
        ∑ i ∈ I, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0} d) :
    dA + dB - 1 ≤ d := by
  obtain ⟨_, ⟨i, hi⟩, a, ha, _⟩ := h.1.2 (fun _ => 0)
  obtain ⟨haA, haB⟩ := ha i hi
  let := Module.compHom M (RingHom.fst R R')
  let := Module.compHom N (RingHom.snd R R')
  apply davenport_prod_ge (A ×ˢ B) (M := M) (N := N) _ _ h
  · simpa only [davenport_prod_ring_ge.davenportSet_compHom (RingHom.fst R R'),
      RingHom.coe_fst, Set.fst_image_prod A ⟨_, haB⟩] using hA
  · simpa only [davenport_prod_ring_ge.davenportSet_compHom (RingHom.snd R R'),
      RingHom.coe_snd, Set.snd_image_prod ⟨_, haA⟩ B] using hB

end MetaMathlibExt
