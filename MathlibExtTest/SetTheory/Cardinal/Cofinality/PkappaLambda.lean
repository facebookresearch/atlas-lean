/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Cardinal.Cofinality.PkappaLambda
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

open Cardinal Ordinal

namespace MathlibExtTest.SetTheory.Cardinal.Cofinality.PkappaLambda

open MetaMathlibExt

-- Logic 55: Subsets of $lambda$ of size less than $\kappa$

/-- Sanity check: `P_κ(λ)` is downward closed under `⊆` — a subset of a set of cardinality
`< κ` again has cardinality `< κ`.  This exercises the direction of the inequality: it
fails if the bound is written `Cardinal.lift κ < #x`. -/

theorem powersetCardLT_downward.{u} {κ lam : Cardinal.{u}}
    {x y : Set (Set.Iio lam.ord)}
    (hx : x ∈ powersetCardLT κ lam) (hyx : y ⊆ x) : y ∈ powersetCardLT κ lam :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hyx) hx

-- Logic 56: Club in P_κ(λ)

/-- `∅ ∈ P_κ(λ)` whenever `0 < κ`. -/

theorem empty_mem_powersetCardLT.{u} {κ lam : Cardinal.{u}} (hκ : 0 < κ) :
    (∅ : Set (Set.Iio lam.ord)) ∈ powersetCardLT κ lam := by
  show #(∅ : Set (Set.Iio lam.ord)) < Cardinal.lift.{u+1} κ
  simpa using hκ

/-- Sanity check: every club is nonempty.  This exercises `cofinal`, and in particular
that it quantifies over all of `P_κ(λ)` rather than over `C` — the latter reading would
make the statement unprovable. -/

theorem _root_.MetaMathlibExt.IsClubPowersetCardLT.nonempty.{u} {κ lam : Cardinal.{u}}
    {C : Set (Set (Set.Iio lam.ord))}
    (h : IsClubPowersetCardLT κ lam C) (hκ : 0 < κ) : C.Nonempty := by
  obtain ⟨y, hy, _⟩ := h.cofinal ∅ (empty_mem_powersetCardLT hκ)
  exact ⟨y, hy⟩

end MathlibExtTest.SetTheory.Cardinal.Cofinality.PkappaLambda

end
