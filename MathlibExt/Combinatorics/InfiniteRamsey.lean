/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Monotone.Basic

/-!
# Infinite Ramsey theorem

The proof is by induction on the size of the finite subsets. At each step of the
successor case we pick a point and thin the remaining infinite set so that adding
that point to a subset of the previous arity always gives the same color.
-/

namespace MetaMathlibExt

/-- The infinite Ramsey theorem: for a positive `k`, every finite coloring of the `k`-element
subsets of an infinite set `X` is constant on the `k`-element subsets of some infinite `Y ⊆ X`.

See R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, §9.1, Theorem 9.1.2. -/
public theorem infinite_ramsey {α ι : Type*} [Finite ι] {X : Set α} (hX : X.Infinite)
    {k : ℕ} (hk : 0 < k) (χ : {s : Finset α // s.card = k ∧ (↑s : Set α) ⊆ X} → ι) :
    ∃ Y : Set α, Y ⊆ X ∧ Y.Infinite ∧ ∃ c : ι, ∀ s, (↑s.1 : Set α) ⊆ Y → χ s = c := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  clear hk
  induction n generalizing X with
  | zero =>
    -- In arity one, apply the infinite pigeonhole principle to the singleton colors.
    have := hX.to_subtype
    let f (x : X) : ι := χ ⟨{x.val}, Finset.card_singleton _, by simp⟩
    obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
    let I : Set X := f ⁻¹' {c}
    have hI : I.Infinite := Set.infinite_coe_iff.mp hc
    refine ⟨Subtype.val '' I, ?_, hI.image Subtype.val_injective.injOn, c, ?_⟩
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · intro s hs
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.property.1
      have hxs : x ∈ s.val := by simp [hx]
      obtain ⟨y, hy, hyx⟩ := hs hxs
      calc
        χ s = f y := congrArg χ (Subtype.ext (by
          change s.val = {y.val}
          rw [hx, hyx]))
        _ = c := hy
  | succ n ih =>
    let State := {U : Set α // U.Infinite ∧ U ⊆ X}
    have step (U : State) :
        ∃ x ∈ U.val, ∃ V : State, V.val ⊆ U.val \ {x} ∧ ∃ c : ι,
          ∀ s : {s : Finset α // s.card = (n + 1) + 1 ∧ (↑s : Set α) ⊆ X},
            x ∈ s.val → (↑(s.val.erase x) : Set α) ⊆ V.val → χ s = c := by
      obtain ⟨x, hx⟩ := U.property.1.nonempty
      let addPoint (s : {s : Finset α // s.card = n + 1 ∧ (↑s : Set α) ⊆ U.val \ {x}}) :
          {s : Finset α // s.card = (n + 1) + 1 ∧ (↑s : Set α) ⊆ X} := by
        have hnot : x ∉ s.val := fun h ↦ (s.property.2 h).2 (Set.mem_singleton x)
        refine ⟨insert x s.val, (Finset.card_insert_of_notMem hnot).trans ?_, ?_⟩
        · rw [s.property.1]
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact U.property.2 hx
          · exact U.property.2 (s.property.2 hy).1
      obtain ⟨V, hVU, hV, c, hc⟩ :=
        ih (U.property.1.sdiff (Set.finite_singleton x)) (fun s ↦ χ (addPoint s))
      refine ⟨x, hx, ⟨V, hV, fun _ hy ↦ U.property.2 (hVU hy).1⟩, hVU, c, ?_⟩
      intro s hxs hs
      have hcard : (s.val.erase x).card = n + 1 :=
        Nat.add_right_cancel ((Finset.card_erase_add_one hxs).trans s.property.1)
      let t : {t : Finset α // t.card = n + 1 ∧ (↑t : Set α) ⊆ U.val \ {x}} :=
        ⟨s.val.erase x, hcard, hs.trans hVU⟩
      calc
        χ s = χ (addPoint t) := congrArg χ (Subtype.ext (Finset.insert_erase hxs).symm)
        _ = c := hc t hs
    choose x hx next hnext col hcol using step
    -- The next set excludes the current point; all later points lie in that next set.
    let chain : ℕ → State := Nat.rec ⟨X, hX, Set.Subset.rfl⟩ (fun _ U ↦ next U)
    let A (m : ℕ) : Set α := (chain m).val
    let point (m : ℕ) : α := x (chain m)
    have hA : Antitone A := antitone_nat_of_succ_le fun m _ h ↦ (hnext (chain m) h).1
    have hlt {m l : ℕ} (h : m < l) : point m ≠ point l := by
      have hm : point l ∈ A (m + 1) := hA (Nat.succ_le_of_lt h) (hx (chain l))
      exact fun e ↦ (hnext (chain m) hm).2 (Set.mem_singleton_iff.mpr e.symm)
    have hinj : Function.Injective point := by
      intro m l h
      rcases lt_trichotomy m l with hml | rfl | hlm
      · exact (hlt hml h).elim
      · rfl
      · exact (hlt hlm h.symm).elim
    let color (m : ℕ) : ι := col (chain m)
    obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber color
    let I : Set ℕ := color ⁻¹' {c}
    have hI : I.Infinite := Set.infinite_coe_iff.mp hc
    refine ⟨point '' I, ?_, hI.image hinj.injOn, c, ?_⟩
    · rintro _ ⟨m, _, rfl⟩
      exact (chain m).property.2 (hx (chain m))
    · intro s hs
      have hex : ∃ m, m ∈ I ∧ point m ∈ s.val := by
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [s.property.1]; exact Nat.succ_pos _)
        obtain ⟨m, hm, rfl⟩ := hs ha
        exact ⟨m, hm, ha⟩
      -- The least index of this subset gives its color; the other points lie in its tail.
      let m := Nat.find hex
      have hm := Nat.find_spec hex
      refine (hcol (chain m) s hm.2 ?_).trans hm.1
      intro y hy
      obtain ⟨hne, hys⟩ := Finset.mem_erase.mp hy
      obtain ⟨l, hl, rfl⟩ := hs hys
      have hml : m < l := lt_of_le_of_ne (Nat.find_min' hex ⟨hl, hys⟩)
        (fun e ↦ hne (congrArg point e.symm))
      exact hA (Nat.succ_le_of_lt hml) (hx (chain l))

end MetaMathlibExt
