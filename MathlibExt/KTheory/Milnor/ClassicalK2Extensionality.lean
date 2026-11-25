/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.ClassicalSymbols

/-!
# `K₂` generation and extensionality via the degree symbol-generation API

`MilnorK F 2` is spanned by the classical `K₂` symbol `k2Symbol`. The general
tuple-generation API `MilnorK.symbolTuple_span` and `MilnorK.symbolTuple_ext`
is obtained directly from the canonical `MilnorKRing` degree symbol-generation
API `MilnorKRing.span_range_symbolTuple_eq_top` and `MilnorKRing.symbolTuple_ext`;
this module specializes that API to `Fin 2` and identifies `Fin 2` tuples with
pairs to obtain `K₂` generation and extensionality.

## Main results
* `MilnorK.k2Symbol_span`
* `MilnorK.k2Symbol_ext`
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

private theorem symbolTuple_two_eq_k2Symbol (v : Fin 2 → Fˣ) :
    symbolTuple F 2 v = k2Symbol F (v 0) (v 1) := by
  apply Subtype.ext
  calc (symbolTuple F 2 v : MilnorKRing F)
      = MilnorKRing.symbolList F (List.ofFn v) := MilnorKRing.symbolTuple_coe F 2 v
    _ = MilnorKRing.symbolList F [v 0, v 1] := by
        have : List.ofFn v = [v 0, v 1] := by
          have h : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
          rw [h]; rfl
        rw [this]
    _ = MilnorKRing.k2Symbol (F := F) (v 0) (v 1) :=
        (MilnorKRing.k2Symbol_eq_symbolList_pair (v 0) (v 1)).symm
    _ = (k2Symbol F (v 0) (v 1) : MilnorKRing F) := rfl

/-- `MilnorK F 2` is spanned by `k2Symbol`. -/
theorem k2Symbol_span :
    Submodule.span ℤ (Set.range (fun p : Fˣ × Fˣ => k2Symbol F p.1 p.2)) = ⊤ := by
  have h_tuple : Submodule.span ℤ (Set.range (fun v : Fin 2 → Fˣ => symbolTuple F 2 v)) = ⊤ :=
    symbolTuple_span F 2
  have h_range_eq : Set.range (fun p : Fˣ × Fˣ => k2Symbol F p.1 p.2) =
      Set.range (fun v : Fin 2 → Fˣ => symbolTuple F 2 v) := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      refine ⟨![a, b], ?_⟩
      calc symbolTuple F 2 ![a, b]
          = k2Symbol F (![a, b] 0) (![a, b] 1) := symbolTuple_two_eq_k2Symbol F _
        _ = k2Symbol F a b := by simp
    · rintro ⟨v, rfl⟩
      exact ⟨(v 0, v 1), (symbolTuple_two_eq_k2Symbol F v).symm⟩
  rw [h_range_eq]
  exact h_tuple

/-- Two linear maps from `MilnorK F 2` coincide if they agree on symbols. -/
theorem k2Symbol_ext {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f g : MilnorK F 2 →ₗ[ℤ] M)
    (h : ∀ a b : Fˣ, f (k2Symbol F a b) = g (k2Symbol F a b)) :
    f = g := by
  have h_tuple : ∀ v : Fin 2 → Fˣ, f (symbolTuple F 2 v) = g (symbolTuple F 2 v) := by
    intro v
    rw [symbolTuple_two_eq_k2Symbol F v]
    exact h (v 0) (v 1)
  exact symbolTuple_ext F f g h_tuple

end MilnorK
