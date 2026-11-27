/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RatFunc_exists_algEquiv_apply_X_eq_moebius.lean`
and
`P2M/Sol/S_RatFunc_exists_algEquiv_apply_X_eq_moebius.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Möbius automorphisms of `K(X)`

For `a d - b c ≠ 0`, there is a `K`-algebra automorphism of the rational function field `K(X)`
sending `X` to `(a X + b) / (c X + d)`.
-/

@[expose] public section

open Polynomial IntermediateField

namespace RatFunc

variable {K : Type*} [Field K]

/-- A Möbius transformation `X ↦ (a X + b) / (c X + d)` with `a d - b c ≠ 0` extends to a
`K`-algebra automorphism of `K(X)`. -/
theorem exists_algEquiv_apply_X_eq_moebius (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ∃ φ : RatFunc K ≃ₐ[K] RatFunc K, φ X = (C a * X + C b) / (C c * X + C d) := by
  set f : RatFunc K := (C a * X + C b) / (C c * X + C d) with hf
  have hden : (C c * X + C d : RatFunc K) ≠ 0 := by
    intro h
    have h1 : (C c * X + C d : RatFunc K) =
        algebraMap K[X] (RatFunc K) (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
      simp
    rw [h1, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))] at h
    have hc : c = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 1) h
    have hd : d = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 0) h
    apply hdet; rw [hc, hd]; ring
  have hkey : (C a - C c * f) * (C c * X + C d) = C (a * d - b * c) := by
    rw [hf, sub_mul, mul_assoc, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
  have hac : (C a - C c * f : RatFunc K) ≠ 0 := by
    intro h; rw [h, zero_mul, eq_comm, map_eq_zero_iff _ C_injective] at hkey; exact hdet hkey
  have hX : (X : RatFunc K) = (C d * f - C b) / (C a - C c * f) := by
    rw [eq_div_iff hac]
    have : (C d * f - C b) * (C c * X + C d) = X * C (a * d - b * c) := by
      rw [sub_mul, mul_assoc, hf, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
    apply mul_right_cancel₀ hden
    rw [mul_assoc, hkey, this]
  have hfC : ¬ ∃ e : K, f = C e := by
    rintro ⟨e, he⟩
    have hXC : (X : RatFunc K) = C ((d * e - b) / (a - c * e)) := by
      rw [hX, he, ← map_mul, ← map_sub, ← map_mul, ← map_sub, ← map_div₀]
    apply transcendental_X (K := K)
    rw [hXC, ← algebraMap_eq_C]
    exact isAlgebraic_algebraMap _
  have htr : Transcendental K f := transcendental_of_ne_C f hfC
  have hXmem : (X : RatFunc K) ∈ K⟮f⟯ := by
    rw [hX]
    have hfmem : f ∈ K⟮f⟯ := mem_adjoin_simple_self K f
    have hCmem : ∀ e : K, (C e : RatFunc K) ∈ K⟮f⟯ := fun e ↦ by
      rw [← algebraMap_C]; exact (K⟮f⟯).algebraMap_mem e
    exact div_mem (sub_mem (mul_mem (hCmem d) hfmem) (hCmem b))
      (sub_mem (hCmem a) (mul_mem (hCmem c) hfmem))
  have htop : K⟮f⟯ = ⊤ := by
    rw [eq_top_iff, ← adjoin_X (K := K), adjoin_simple_le_iff]
    exact hXmem
  refine ⟨(algEquivOfTranscendental f htr).trans ((equivOfEq htop).trans topEquiv), ?_⟩
  simp [algEquivOfTranscendental_X]

end RatFunc
