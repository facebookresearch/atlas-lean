/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

/-!
# Window indistinguishability

One-round algorithms on directed cycles: adjacent windows
of four distinct identifiers receive different colors.
The counting lower bound is not included here.
-/

@[expose] public section

/-- Window indistinguishability for one-round algorithms
on directed cycles (DPA-22 core). A one-round algorithm
assigns to each vertex a color from the identifiers of
its predecessor, itself, and its successor. If it
properly colors every directed cycle under every
injective identifier assignment, then the colors of two
adjacent centers with windows `(a, b, c)` and `(b, c, d)`
(for pairwise distinct identifiers) always differ: a
four-cycle with identifiers `a, b, c, d` realizes both
windows at adjacent vertices. -/
theorem window_colors_differ {m c : ℕ}
    (A : Fin m → Fin m → Fin m → Fin c)
    (hproper : ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n) (id : Fin n → Fin m),
      Function.Injective id → ∀ i : Fin n,
        A (id (i - 1)) (id i) (id (i + 1))
          ≠ A (id (i + 1 - 1)) (id (i + 1)) (id (i + 1 + 1)))
    {a b cc d : Fin m}
    (hab : a ≠ b) (hac : a ≠ cc) (had : a ≠ d)
    (hbc : b ≠ cc) (hbd : b ≠ d) (hcd : cc ≠ d) :
    A a b cc ≠ A b cc d := by
  have e0 : ∀ hk : 0 < 4, ((![a, b, cc, d] : Fin 4 → Fin m) ⟨0, hk⟩) = a :=
    fun _ => rfl
  have e1 : ∀ hk : 1 < 4, ((![a, b, cc, d] : Fin 4 → Fin m) ⟨1, hk⟩) = b :=
    fun _ => rfl
  have e2 : ∀ hk : 2 < 4, ((![a, b, cc, d] : Fin 4 → Fin m) ⟨2, hk⟩) = cc :=
    fun _ => rfl
  have e3 : ∀ hk : 3 < 4, ((![a, b, cc, d] : Fin 4 → Fin m) ⟨3, hk⟩) = d :=
    fun _ => rfl
  have hid : Function.Injective (![a, b, cc, d] : Fin 4 → Fin m) := by
    intro x y h
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    interval_cases x <;> interval_cases y <;> simp_all
  have h := hproper 4 (le_refl 4) (![a, b, cc, d] : Fin 4 → Fin m) hid (1 : Fin 4)
  have w1 : ((1 : Fin 4) - 1) = 0 := by decide
  have w3 : ((1 : Fin 4) + 1 - 1) = 1 := by decide
  have w4 : ((1 : Fin 4) + 1 + 1) = 3 := by decide
  have w2 : ((1 : Fin 4) + 1) = 2 := by decide
  have v0 : ((![a, b, cc, d] : Fin 4 → Fin m) 0) = a := rfl
  have v1 : ((![a, b, cc, d] : Fin 4 → Fin m) 1) = b := rfl
  have v2 : ((![a, b, cc, d] : Fin 4 → Fin m) 2) = cc := rfl
  have v3 : ((![a, b, cc, d] : Fin 4 → Fin m) 3) = d := rfl
  rw [w1, w3, w4, w2, v0, v1, v2, v3] at h
  exact h

end
