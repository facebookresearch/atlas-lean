/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard.lean`
and
`P2M/Sol/S_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard.lean`
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

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement

/-!
# A Tate-style cardinality and generation criterion in degree two

Let `G` be a finite group and `X` an integral representation. Suppose every
subgroup `S` has finite second cohomology with
`|H²(S, X)| ≤ |S|`, suppose corestriction maps are given with
`cor ∘ res = index` on `H²`, and suppose some `u ∈ H²(G, X)` has
additive order `|G|`. Then `|H²(S, X)| = |S|` for every subgroup `S`, and
the restriction of `u` generates `H²(S, X)` as an abelian group.
-/

@[expose] public section

open CategoryTheory

/-- If `u ∈ H²(G, X)` has additive order `|G|`, every subgroup has
`|H²(S, X)| ≤ |S|`, and corestrictions satisfy `cor ∘ res = index`,
then `|H²(S, X)| = |S|` for all `S` and each restriction of `u` spans
`H²(S, X)`. -/
theorem groupCohomology.natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard
    {G : Type} [Group G] [Finite G]
    (X : Rep ℤ G) (u : groupCohomology X 2)
    (hu : addOrderOf u = Nat.card G)
    (h5 : ∀ (S : Subgroup G) [Fintype S],
      Finite (groupCohomology (Rep.res S.subtype X) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) ≤ Fintype.card S)
    (cor : ∀ S : Subgroup G,
      groupCohomology (Rep.res S.subtype X) 2 →ₗ[ℤ] groupCohomology X 2)
    (hcor : ∀ (S : Subgroup G) (x : groupCohomology X 2),
      cor S ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) =
        S.index • x) :
    (∀ (S : Subgroup G) [Fintype S],
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) := by
  classical
  set res : ∀ S : Subgroup G,
      groupCohomology X 2 → groupCohomology (Rep.res S.subtype X) 2 :=
    fun S x => (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x with hres
  have key : ∀ (S : Subgroup G) [Fintype S], addOrderOf (res S u) = Fintype.card S ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S := by
    intro S _
    haveI := (h5 S).1
    have hS0 : 0 < Fintype.card S := Fintype.card_pos
    have hidx : Fintype.card S * S.index = Nat.card G := by
      have := S.card_mul_index
      rwa [Nat.card_eq_fintype_card] at this
    have hi0 : S.index ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hidx; exact (Nat.card_pos (α := G)).ne' hidx.symm
    have hord_nsmul : addOrderOf (S.index • u) = Fintype.card S := by
      rw [addOrderOf_nsmul' u hi0, hu, ← hidx,
        Nat.gcd_eq_right (dvd_mul_left S.index (Fintype.card S)),
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hi0)]
    have hdvd : Fintype.card S ∣ addOrderOf (res S u) := by
      rw [← hord_nsmul, ← hcor S u]
      exact addOrderOf_map_dvd (cor S).toAddMonoidHom (res S u)
    letI : Fintype (groupCohomology (Rep.res S.subtype X) 2) := Fintype.ofFinite _
    have hle' : addOrderOf (res S u) ≤ Fintype.card S := by
      calc addOrderOf (res S u)
          ≤ Fintype.card (groupCohomology (Rep.res S.subtype X) 2) :=
            addOrderOf_le_card_univ
        _ = Nat.card (groupCohomology (Rep.res S.subtype X) 2) :=
            (Nat.card_eq_fintype_card).symm
        _ ≤ Fintype.card S := (h5 S).2
    have hpos : 0 < addOrderOf (res S u) := addOrderOf_pos (res S u)
    have hordeq : addOrderOf (res S u) = Fintype.card S :=
      le_antisymm hle' (Nat.le_of_dvd hpos hdvd)
    refine ⟨hordeq, le_antisymm ((h5 S).2) ?_⟩
    calc Fintype.card S = addOrderOf (res S u) := hordeq.symm
      _ ≤ Fintype.card (groupCohomology (Rep.res S.subtype X) 2) :=
          addOrderOf_le_card_univ
      _ = Nat.card (groupCohomology (Rep.res S.subtype X) 2) :=
          (Nat.card_eq_fintype_card).symm
  refine ⟨fun S _ => (key S).2, fun S => ?_⟩
  letI : Fintype S := Fintype.ofFinite S
  haveI := (h5 S).1
  obtain ⟨hord, hcard⟩ := key S
  have hzm : AddSubgroup.zmultiples (res S u) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hcard]
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ AddSubgroup.zmultiples (res S u) := by rw [hzm]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine Submodule.mem_span_singleton.mpr ⟨n, ?_⟩
  rw [← hn, ← Int.cast_smul_eq_zsmul ℤ n (res S u), Int.cast_id]
