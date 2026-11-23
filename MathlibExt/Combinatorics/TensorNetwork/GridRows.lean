/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
replace global finite alphabets and padded cut coordinates with explicit finite alphabets and
active column-pair labels, while retaining the source row factors and capacities.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Grid

/-! # Finite row networks for grid tensors

This module contracts each grid row to one vertex of a factored tensor network. Row states use
the supplied finite edge and diagonal alphabets, while labels between two rows contain vertical
edge labels and one cut label for each active column pair.

Adapted from `Groundwork.Grid.{Defs,RowNet}` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {ρ γ A T : Type*}

/-- Merge every grid row into one vertex of a factored tensor network. The state and label
carriers may be infinite; only the supplied alphabets are enumerated. Capacity metadata charges
`L` per vertical edge and the supplied cut capacity for each active rectangle. -/
def gridRowNetwork [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [DecidableEq A]
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) (L : ℕ) :
    Factored ρ (γ → ρ × γ → A)
      ((γ → A) × ({k : γ × γ // k ∈ orderedPairs γ} → T)) := by
  classical
  exact
    { S := fun a => Fintype.piFinset fun i =>
        Fintype.piFinset fun w => if w = (a, i) then diagonalLabels else labels
      W := fun a z =>
        (∏ i, R (a, i) (z i)) *
          ∏ q ∈ orderedPairs γ,
            if z q.1 (a, q.2) = z q.2 (a, q.1) then 1 else 0
      Θ := fun a b => if a < b then
        (Fintype.piFinset fun _ : γ => labels) ×ˢ
          Fintype.piFinset fun k : {k : γ × γ // k ∈ orderedPairs γ} =>
            cutLabels ((a, b), k)
        else ∅
      f := fun a b z θ => if a < b then
        (∏ i, if z i (b, i) = θ.1 i then 1 else 0) *
          ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
            top ((a, b), k) (z k.1.1 (b, k.1.2))
              (z k.1.2 (b, k.1.1)) (θ.2 k)
        else
          (∏ i, if z i (b, i) = θ.1 i then 1 else 0) *
            ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
              bottom ((b, a), k) (z k.1.1 (b, k.1.2))
                (z k.1.2 (b, k.1.1)) (θ.2 k)
      c := fun a b => Fintype.card γ * L +
        ∑ k : γ × γ with k ∈ orderedPairs γ, cap ((min a b, max a b), k) }

private theorem sum_eq_and_mem [DecidableEq A] (labels : Finset A) (x y : A) :
    (∑ θ ∈ labels,
      (if x = θ then (1 : ℤ) else 0) * if y = θ then 1 else 0) =
      if x = y ∧ x ∈ labels then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    simp
  · simp [hxy]

/-- The interaction between increasing rows is the rectangle-kernel product times vertical
equality indicators. For finite alphabets, an equal vertical value contributes only when it is
in `labels`. -/
theorem gridRowNetwork_interaction [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) (L : ℕ)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (hG : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ)
    {a b : ρ} (hab : a < b) (z z' : γ → ρ × γ → A) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).interaction
        a b z z' =
      (∏ i, if z i (b, i) = z' i (a, i) ∧ z i (b, i) ∈ labels then 1 else 0) *
        ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
          G ((a, b), k)
            (z k.1.1 (b, k.1.2)) (z k.1.2 (b, k.1.1))
            (z' k.1.1 (a, k.1.2)) (z' k.1.2 (a, k.1.1)) := by
  classical
  have hvertical :
      (∑ θ ∈ Fintype.piFinset (fun _ : γ => labels),
          (∏ i, if z i (b, i) = θ i then (1 : ℤ) else 0) *
            ∏ i, if z' i (a, i) = θ i then 1 else 0) =
        ∏ i, if z i (b, i) = z' i (a, i) ∧ z i (b, i) ∈ labels then 1 else 0 := by
    simp_rw [← Finset.prod_mul_distrib]
    calc
      _ = ∏ i, ∑ θ ∈ labels,
          (if z i (b, i) = θ then (1 : ℤ) else 0) *
            if z' i (a, i) = θ then 1 else 0 :=
        (Finset.prod_univ_sum (fun _ : γ => labels) fun i θ =>
          (if z i (b, i) = θ then (1 : ℤ) else 0) *
            if z' i (a, i) = θ then 1 else 0).symm
      _ = _ := Fintype.prod_congr _ _ fun i => sum_eq_and_mem labels _ _
  have hcut :
      (∑ θ ∈ Fintype.piFinset
          (fun k : {k : γ × γ // k ∈ orderedPairs γ} => cutLabels ((a, b), k)),
          (∏ k : {k : γ × γ // k ∈ orderedPairs γ},
              top ((a, b), k) (z k.1.1 (b, k.1.2))
                (z k.1.2 (b, k.1.1)) (θ k)) *
            ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
              bottom ((a, b), k) (z' k.1.1 (a, k.1.2))
                (z' k.1.2 (a, k.1.1)) (θ k)) =
        ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
          G ((a, b), k)
            (z k.1.1 (b, k.1.2)) (z k.1.2 (b, k.1.1))
            (z' k.1.1 (a, k.1.2)) (z' k.1.2 (a, k.1.1)) := by
    simp_rw [← Finset.prod_mul_distrib]
    calc
      _ = ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
          ∑ θ ∈ cutLabels ((a, b), k),
            top ((a, b), k) (z k.1.1 (b, k.1.2))
                (z k.1.2 (b, k.1.1)) θ *
              bottom ((a, b), k) (z' k.1.1 (a, k.1.2))
                (z' k.1.2 (a, k.1.1)) θ :=
        (Finset.prod_univ_sum
          (fun k : {k : γ × γ // k ∈ orderedPairs γ} => cutLabels ((a, b), k))
          fun k θ =>
            top ((a, b), k) (z k.1.1 (b, k.1.2))
                (z k.1.2 (b, k.1.1)) θ *
              bottom ((a, b), k) (z' k.1.1 (a, k.1.2))
                (z' k.1.2 (a, k.1.1)) θ).symm
      _ = _ := Fintype.prod_congr _ _ fun k => (hG ((a, b), k) _ _ _ _).symm
  unfold Factored.interaction Factored.labelSet
  simp only [gridRowNetwork, min_eq_left hab.le, max_eq_right hab.le, hab,
    ↓reduceIte, not_lt.mpr hab.le]
  rw [Finset.sum_product]
  calc
    _ = (∑ θ ∈ Fintype.piFinset (fun _ : γ => labels),
          (∏ i, if z i (b, i) = θ i then (1 : ℤ) else 0) *
            ∏ i, if z' i (a, i) = θ i then 1 else 0) *
        ∑ θ ∈ Fintype.piFinset
          (fun k : {k : γ × γ // k ∈ orderedPairs γ} => cutLabels ((a, b), k)),
          (∏ k : {k : γ × γ // k ∈ orderedPairs γ},
              top ((a, b), k) (z k.1.1 (b, k.1.2))
                (z k.1.2 (b, k.1.1)) (θ k)) *
            ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
              bottom ((a, b), k) (z' k.1.1 (a, k.1.2))
                (z' k.1.2 (a, k.1.1)) (θ k) := by
      rw [Finset.sum_mul_sum]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hvertical, hcut]

/-- When the left state is enumerated by the row network, the alphabet-membership condition is
automatic, so the interaction recovers the source vertical-equality formula. The right state may
be arbitrary because equality with an allowed left value already forces its vertical value. -/
theorem gridRowNetwork_interaction_of_mem [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) (L : ℕ)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (hG : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ)
    {a b : ρ} (hab : a < b) (z z' : γ → ρ × γ → A)
    (hz : z ∈ (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).S a) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).interaction
        a b z z' =
      (∏ i, if z i (b, i) = z' i (a, i) then 1 else 0) *
        ∏ k : {k : γ × γ // k ∈ orderedPairs γ},
          G ((a, b), k)
            (z k.1.1 (b, k.1.2)) (z k.1.2 (b, k.1.1))
            (z' k.1.1 (a, k.1.2)) (z' k.1.2 (a, k.1.1)) := by
  rw [gridRowNetwork_interaction labels diagonalLabels R cutLabels top bottom cap L G hG hab]
  congr 1
  apply Fintype.prod_congr
  intro i
  have hzi := Fintype.mem_piFinset.mp hz i
  have hmem := Fintype.mem_piFinset.mp hzi (b, i)
  have hba : (b, i) ≠ (a, i) := by
    intro h
    exact hab.ne' (congrArg Prod.fst h)
  simp [hba] at hmem
  simp [hmem]

/-- If each rectangle kernel is the finite sum of its top and bottom factors, contracting the
constructed row network gives the canonical finite grid value. -/
theorem gridRowNetwork_value [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) (L : ℕ)
    (hG : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ) :
    (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).value =
      gridValue labels diagonalLabels R G := by
  classical
  let e : Matrix (ρ × γ) (ρ × γ) A ≃
      (ρ → γ → ρ × γ → A) := Equiv.curry ρ γ (ρ × γ → A)
  have e_apply (ℓ : Matrix (ρ × γ) (ρ × γ) A) (a : ρ) (i : γ)
      (w : ρ × γ) : e ℓ a i w = ℓ (a, i) w := rfl
  have he_mem (ℓ : Matrix (ρ × γ) (ρ × γ) A) :
      ℓ ∈ gridLabelings labels diagonalLabels ↔
        e ℓ ∈ Fintype.piFinset
          (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).S := by
    rw [mem_gridLabelings, Fintype.mem_piFinset]
    simp only [gridRowNetwork, Fintype.mem_piFinset]
    constructor
    · intro h a i w
      by_cases hw : w = (a, i)
      · simpa [e_apply, hw] using (h (a, i) w).1 hw
      · simpa [e_apply, hw] using (h (a, i) w).2 hw
    · intro h
      rintro ⟨a, i⟩ w
      constructor
      · intro hw
        simpa [e_apply, hw] using h a i w
      · intro hw
        simpa [e_apply, hw] using h a i w
  unfold Factored.value gridValue
  symm
  refine Finset.sum_equiv e he_mem ?_
  intro ℓ hℓ
  have e_row (a : ρ) (i : γ) : e ℓ a i = ℓ (a, i) := by
    funext w
    exact e_apply ℓ a i w
  have hz : ∀ a,
      e ℓ a ∈ (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).S a :=
    Fintype.mem_piFinset.mp (he_mem ℓ |>.mp hℓ)
  have hsubtype (F : γ × γ → ℤ) :
      (∏ k : {k : γ × γ // k ∈ orderedPairs γ}, F k) =
        ∏ k ∈ orderedPairs γ, F k := by
    symm
    exact Finset.prod_subtype (orderedPairs γ) (fun _ => Iff.rfl) F
  have hinteraction : ∀ p ∈ orderedPairs ρ,
      (gridRowNetwork labels diagonalLabels R cutLabels top bottom cap L).interaction
          p.1 p.2 (e ℓ p.1) (e ℓ p.2) =
        (∏ i, if e ℓ p.1 i (p.2, i) = e ℓ p.2 i (p.1, i) then 1 else 0) *
          ∏ k ∈ orderedPairs γ,
            G ((p.1, p.2), k)
              (e ℓ p.1 k.1 (p.2, k.2))
              (e ℓ p.1 k.2 (p.2, k.1))
              (e ℓ p.2 k.1 (p.1, k.2))
              (e ℓ p.2 k.2 (p.1, k.1)) := by
    intro p hp
    rw [gridRowNetwork_interaction_of_mem labels diagonalLabels R cutLabels top bottom
      cap L G hG (by simpa using hp) _ _ (hz p.1)]
    congr 1
    exact hsubtype fun k =>
      G ((p.1, p.2), k)
        (e ℓ p.1 k.1 (p.2, k.2)) (e ℓ p.1 k.2 (p.2, k.1))
        (e ℓ p.2 k.1 (p.1, k.2)) (e ℓ p.2 k.2 (p.1, k.1))
  rw [Finset.prod_congr rfl hinteraction]
  simp only [gridRowNetwork, e_apply, e_row, Finset.prod_mul_distrib,
    Fintype.prod_prod_type, gridRectangles, rectangleApply, Prod.mk.eta]
  rw [Finset.prod_product]
  rw [Finset.prod_comm (s := univ) (t := orderedPairs ρ)]
  ring

end TensorNetwork
