/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.DeRhamFiniteExtension

/-! Tests for de Rham representations over a finite extension: for `K ≤ L` inside `ℚ̄_p` with `L`
finite over `ℚ_p`, a representation is de Rham over `K` if and only if it is de Rham over `L`, in
particular over `K = ℚ_p`, and then in the basis form of admissibility too. -/

open Representation PadicComplexInt

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

-- de Rham over `K` if and only if over `L`.
example {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) [FiniteDimensional ℚ_[p] L]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) : ρ.IsDeRham K ↔ ρ.IsDeRham L :=
  isDeRham_iff_of_le h ρ

-- de Rham over `ℚ_p` if and only if over a finite extension `L` of `ℚ_p`.
example (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) : ρ.IsDeRham ⊥ ↔ ρ.IsDeRham L :=
  isDeRham_iff_of_le bot_le ρ

-- For a finite-dimensional `V`, de Rham over `L` gives a `B_dR`-basis of `B_dR ⊗ V` of
-- `G_K`-invariant vectors.
example {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) [FiniteDimensional ℚ_[p] L]
    [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (hρ : ρ.IsDeRham L) : ρ.HasFixedBasis (galoisBDeRham p) K.fixingSubgroup :=
  (isDeRham_iff_hasFixedBasis ρ K).1 ((isDeRham_iff_of_le h ρ).2 hρ)
