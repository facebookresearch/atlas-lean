/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`
and
`Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction

/-!
# Restricting and pulling back graph actions

An action of a group by graph automorphisms (`CerednikDrinfeld.Mumford.GraphAction`, from
`MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction`) restricts to every subgroup and pulls
back along group homomorphisms.
-/

@[expose] public section

namespace CerednikDrinfeld
namespace Mumford

variable {G : Type*} [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)

/-- A graph action restricts to every subgroup. -/
instance GraphAction.subgroup (H : Subgroup G) [GraphAction G 𝒯] : GraphAction H 𝒯 :=
  ⟨fun h _ _ hadj => GraphAction.smul_adj (h : G) hadj⟩

/-- A graph action pulls back along a group homomorphism. -/
theorem GraphAction.of_compHom {G' : Type*} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  @GraphAction.mk G' _ W (MulAction.compHom W φ) 𝒯 fun g _ _ hadj =>
    GraphAction.smul_adj (φ g) hadj

end Mumford
end CerednikDrinfeld
