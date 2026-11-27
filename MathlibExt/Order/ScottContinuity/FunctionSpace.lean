/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ScottContinuity.Complete
public import Mathlib.Order.FixedPoints
public import MathlibExt.Order.OmegaCompletePartialOrder.ContinuousHom

/-!
# Scott-continuous function spaces and Kleene's fixed-point theorem for dcpos

Mathlib's `ScottContinuous` is continuity for *directed* suprema, and
`CompletePartialOrder` is a pointed directed-complete partial order (dcpo). Mathlib's
function-space and fixed-point API for domains is stated for ω-chains instead
(`OmegaCompletePartialOrder.ContinuousHom`, `fixedPoints.iterateChain`). This file adds the
directed-set versions used in Scott's domain theory:

* `scottContinuous_sSup_image_of_directedOn` and `isLUB_sSup_image_of_directedOn`: the
  pointwise supremum of a directed family of Scott-continuous maps into a dcpo is
  Scott-continuous and is the supremum of the family, so the Scott-continuous maps form a
  dcpo with pointwise directed suprema (Abramsky and Jung, *Domain Theory*, Handbook of
  Logic in Computer Science vol. 3 (1994), Proposition 2.1.18);
* `scottContinuous_sSup`: between complete lattices, the pointwise supremum of an *arbitrary*
  family of Scott-continuous maps is Scott-continuous (D. Scott, *Continuous Lattices*, Oxford
  PRG-7 (1971), proof of Theorem 3.3);
* `map_iSup_iterate_bot` and `iSup_iterate_bot_le`: Kleene's fixed-point theorem for a
  Scott-continuous self-map of a pointed dcpo (Abramsky and Jung, Theorem 2.1.19 (1)),
  obtained through `iSup_iterate_bot_eq_lfp` from the repository's ω-chain least fixed point
  `OmegaCompletePartialOrder.ContinuousHom.lfp`.
-/

@[expose] public section

namespace MathlibExt.Order.ScottContinuity.FunctionSpace

open OmegaCompletePartialOrder

variable {α β : Type*}

section Directed

variable [Preorder α] [CompletePartialOrder β]

omit [Preorder α] in
private theorem directedOn_image_apply {F : Set (α → β)} (hF : DirectedOn (· ≤ ·) F) (x : α) :
    DirectedOn (· ≤ ·) ((fun f => f x) '' F) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨h, hh, hfh, hgh⟩ := hF f hf g hg
  exact ⟨h x, ⟨h, hh, rfl⟩, hfh x, hgh x⟩

/-- **The pointwise directed supremum of Scott-continuous maps is Scott-continuous.** Let `α` be a
preorder and `β` a pointed dcpo. If `F` is a directed set of Scott-continuous maps `α → β`
(pointwise order), then `x ↦ ⨆ f ∈ F, f x` is Scott-continuous (Abramsky and Jung, *Domain
Theory*, Handbook of Logic in Computer Science vol. 3 (1994), Proposition 2.1.18). -/
theorem scottContinuous_sSup_image_of_directedOn {F : Set (α → β)}
    (hF : DirectedOn (· ≤ ·) F) (hcont : ∀ f ∈ F, ScottContinuous f) :
    ScottContinuous fun x => sSup ((fun f => f x) '' F) := by
  have hmono : Monotone fun x => sSup ((fun f => f x) '' F) := by
    intro x y hxy
    refine (directedOn_image_apply hF x).sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ((hcont f hf).monotone hxy).trans
      ((directedOn_image_apply hF y).le_sSup ⟨f, hf, rfl⟩)
  intro d hne hd a ha
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmono (ha.1 hx)
  · refine (directedOn_image_apply hF a).sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine ((hcont f hf) hne hd ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ((directedOn_image_apply hF x).le_sSup ⟨f, hf, rfl⟩).trans (hb ⟨x, hx, rfl⟩)

omit [Preorder α] in
/-- **Directed suprema of Scott-continuous maps are computed pointwise.** For a directed set `F` of
maps `α → β` into a pointed dcpo, the pointwise supremum `x ↦ ⨆ f ∈ F, f x` is the least upper
bound of `F` for the pointwise order; with `scottContinuous_sSup_image_of_directedOn`, the
Scott-continuous maps `α → β` form a dcpo whose directed suprema are pointwise (Abramsky and
Jung, *Domain Theory*, Handbook of Logic in Computer Science vol. 3 (1994),
Proposition 2.1.18). -/
theorem isLUB_sSup_image_of_directedOn {F : Set (α → β)} (hF : DirectedOn (· ≤ ·) F) :
    IsLUB F fun x => sSup ((fun f => f x) '' F) :=
  ⟨fun f hf x => (directedOn_image_apply hF x).le_sSup ⟨f, hf, rfl⟩,
    fun g hg x => (directedOn_image_apply hF x).sSup_le (by
      rintro _ ⟨f, hf, rfl⟩
      exact hg hf x)⟩

end Directed

/-- **Arbitrary pointwise suprema of Scott-continuous maps between complete lattices.** If every
member of a set `s` of maps between complete lattices is Scott-continuous, so is the pointwise
supremum `sSup s`; hence the Scott-continuous maps form a complete join-subsemilattice of all
maps (D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), proof of Theorem 3.3: "arbitrary
⊔ are [computed pointwise]", stated there for continuous lattices and topological continuity; the
statement here is for all complete lattices and Mathlib's `ScottContinuous`). -/
theorem scottContinuous_sSup [CompleteLattice α] [CompleteLattice β] {s : Set (α → β)}
    (hs : ∀ f ∈ s, ScottContinuous f) : ScottContinuous (sSup s) := by
  refine ScottContinuous.of_map_sSup fun d hne hd => ?_
  have h : ∀ f ∈ s, f (sSup d) = ⨆ x ∈ d, f x := fun f hf => by
    rw [(hs f hf).map_sSup hne hd, sSup_image]
  simp only [sSup_apply, sSup_image, iSup_subtype']
  rw [iSup_comm]
  refine iSup_congr fun ⟨f, hf⟩ => ?_
  change f (sSup d) = ⨆ i : d, f i
  rw [h f hf, iSup_subtype']

section Kleene

variable [CompletePartialOrder α] {f : α → α}

/-- **Kleene's supremum for dcpos is the repository's least fixed point.** For a Scott-continuous
self-map `f` of a pointed dcpo, `⨆ n, f^[n] ⊥` is, by definition, the least fixed point
`ContinuousHom.lfp` of `f` viewed as an ω-Scott-continuous map. -/
theorem iSup_iterate_bot_eq_lfp (hf : ScottContinuous f) :
    ⨆ n, f^[n] ⊥ = ContinuousHom.lfp (ContinuousHom.ofFun f hf.ωScottContinuous) := rfl

/-- **Kleene's fixed-point theorem for pointed dcpos.** If `f` is a Scott-continuous self-map of a
pointed dcpo, then `⨆ n, f^[n] ⊥` is a fixed point of `f` (Abramsky and Jung, *Domain Theory*,
Handbook of Logic in Computer Science vol. 3 (1994), Theorem 2.1.19 (1); D. Scott, *Continuous
Lattices*, Oxford PRG-7 (1971), Proposition 3.14, for continuous lattices). -/
theorem map_iSup_iterate_bot (hf : ScottContinuous f) : f (⨆ n, f^[n] ⊥) = ⨆ n, f^[n] ⊥ := by
  rw [iSup_iterate_bot_eq_lfp hf]
  exact ContinuousHom.lfp_eq (ContinuousHom.ofFun f hf.ωScottContinuous)

/-- **Kleene's fixed point is the least prefixed point.** If `f` is a Scott-continuous self-map of a
pointed dcpo and `f a ≤ a`, then `⨆ n, f^[n] ⊥ ≤ a`; so `⨆ n, f^[n] ⊥` is the least fixed point, and
even the least prefixed point, of `f` (Abramsky and Jung, *Domain Theory*, Handbook of Logic in
Computer Science vol. 3 (1994), Theorem 2.1.19 (1)). -/
theorem iSup_iterate_bot_le (hf : ScottContinuous f) {a : α} (ha : f a ≤ a) :
    ⨆ n, f^[n] ⊥ ≤ a := by
  rw [iSup_iterate_bot_eq_lfp hf]
  exact ContinuousHom.lfp_le (ContinuousHom.ofFun f hf.ωScottContinuous) ha

end Kleene

end MathlibExt.Order.ScottContinuity.FunctionSpace
