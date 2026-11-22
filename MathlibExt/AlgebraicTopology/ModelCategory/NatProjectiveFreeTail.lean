/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import MathlibExt.CategoryTheory.Filtered.NatTailFreeDiagrams

/-!
# Compatibility names for the canonical natural-tail free diagrams

The original complete tail, predecessor, free diagram and Arrow comparison
APIs delegate to the generic categorical owner, preserving their interfaces.
-/

noncomputable section

namespace HomotopicalAlgebra.NatProjectiveFreeTail

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.tail]
abbrev tail := @CategoryTheory.NatTail.FreeDiagrams.tail

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.homEquiv]
abbrev homEquiv := @CategoryTheory.NatTail.FreeDiagrams.homEquiv

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.predecessor]
abbrev predecessor := @CategoryTheory.NatTail.FreeDiagrams.predecessor

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.predecessorTailAdjunction]
abbrev predecessorTailAdjunction := @CategoryTheory.NatTail.FreeDiagrams.predecessorTailAdjunction

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.restrictionAdjunction]
abbrev restrictionAdjunction := @CategoryTheory.NatTail.FreeDiagrams.restrictionAdjunction

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.homEquiv_comp]
alias homEquiv_comp := CategoryTheory.NatTail.FreeDiagrams.homEquiv_comp

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.component]
abbrev component := @CategoryTheory.NatTail.FreeDiagrams.component

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.component_hom_injection]
alias component_hom_injection := CategoryTheory.NatTail.FreeDiagrams.component_hom_injection

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.component_inv_injection]
alias component_inv_injection := CategoryTheory.NatTail.FreeDiagrams.component_inv_injection

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.component_naturality]
alias component_naturality := CategoryTheory.NatTail.FreeDiagrams.component_naturality

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.diagramIso]
abbrev diagramIso := @CategoryTheory.NatTail.FreeDiagrams.diagramIso

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.component_coefficient]
alias component_coefficient := CategoryTheory.NatTail.FreeDiagrams.component_coefficient

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.freeTailIso]
abbrev freeTailIso := @CategoryTheory.NatTail.FreeDiagrams.freeTailIso

@[inherit_doc CategoryTheory.NatTail.FreeDiagrams.freeArrowIso]
abbrev freeArrowIso := @CategoryTheory.NatTail.FreeDiagrams.freeArrowIso

end HomotopicalAlgebra.NatProjectiveFreeTail
