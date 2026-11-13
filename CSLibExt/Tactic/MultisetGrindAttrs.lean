/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-
Ported from Cslib/Tactic/GrindAttrs.lean, PR944 commit
a69a43dca61ead87b6a631854de017ddaa310e08, lines 28-29.
Only the missing multiset registration is reused; no modal changes.
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand

/-! # Multiset grind set registration for the compatibility port -/

@[expose] public section

/-- Multiset context reasoning, including list coercions, exchange, and cancellation. -/
register_grind_attr multiset
