/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Forcing.ForcingAxioms.ProperForcingAxiom
public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

/-! # PFA

`MA_{ℵ₁}` with "ccc" replaced by "proper".  The two checks below isolate where its content sits:
the filter itself is free (the `D = ∅` case is a ZFC theorem), and the density hypothesis is what
makes the conclusion satisfiable at all.

The coherence check `ProperForcingAxiom → MartinAxiom (aleph 1)` is deliberately **not** here — it
routes through the `sorry`-ed `isProper_of_isCCC`, so it lives in `Proper.lean` with the item it
depends on.  Everything in this file is `sorry`-free.

Dependencies copied verbatim from `Corpus.lean`.  `open Cardinal` only, so it pastes into
`Corpus.lean` unchanged. -/

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Forcing.ForcingAxioms.ProperForcingAxiom

open MetaMathlibExt

-- Logic 49: Proper Forcing Axiom

/-- The up-set of `p` is a filter — the witness for the `D = ∅` case below. -/

theorem isPFilter_principal {P : Type*} [PartialOrder P] (p : P) :
    Order.IsPFilter {x : P | p ≤ x} :=
  Order.IsPFilter.of_def ⟨p, le_refl p⟩ (fun _ hx _ hy => ⟨p, le_refl p, hx, hy⟩)
    (fun hxy hx => le_trans hx hxy)

/-- **The filter is free; only meeting the dense sets is hard.**  With `D = ∅` the conclusion of
`ProperForcingAxiom` is a ZFC theorem for every poset — the principal filter at `p` works — with
no appeal to `IsProper`.  So all of PFA's strength lies in the `∀ S ∈ D, (G ∩ S).Nonempty`
clause, and none of it in producing a proper filter containing `p`. -/

theorem exists_pFilter_of_empty {P : Type*} [PartialOrder P] (p : P) :
    ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ (∅ : Set (Set P)), (G ∩ S).Nonempty :=
  ⟨{x : P | p ≤ x}, isPFilter_principal p, le_refl p, fun S hS => absurd hS (Set.notMem_empty S)⟩

/-- **The density hypothesis cannot be dropped.**  Deleting `IsCoinitial` from
`ProperForcingAxiom` leaves a statement false for *every* nonempty poset: take `D = {∅}`, of size
`1 ≤ ℵ₁`, which no `G` can meet.  So `IsCoinitial` is not decoration — it is what keeps the
conclusion satisfiable, and it is why density appears as a hypothesis inside `IsGenericFor` too. -/

theorem not_pfa_conclusion_without_isCoinitial {P : Type*} [PartialOrder P] [Nonempty P] :
    ¬ ∀ D : Set (Set P), Cardinal.mk D ≤ aleph 1 →
        ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty := by
  intro h
  obtain ⟨G, -, -, hG⟩ :=
    h {∅} (by rw [Cardinal.mk_singleton]; exact one_le_aleph0.trans (aleph0_le_aleph 1))
      (Classical.arbitrary P)
  obtain ⟨x, -, hx⟩ := hG ∅ rfl
  exact hx

end MathlibExtTest.SetTheory.Forcing.ForcingAxioms.ProperForcingAxiom

end
