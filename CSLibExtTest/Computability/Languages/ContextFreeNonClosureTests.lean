/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.NonClosure

/-!
# Ordinary-client tests for CFL nonclosure under intersection/complement
-/

public section

namespace Cslib.Language.ContextFreeNonClosureTests

/-- A concrete word of `a^n b^n`. -/
theorem anbn_example_mem :
    ([0, 0, 1, 1] : List (Fin 3)) ∈ eqPowLang (0 : Fin 3) 1 :=
  ⟨2, by decide⟩

/-- The language `a^n b^n` over `Fin 3` is context-free. -/
theorem anbn_example_isContextFree :
    (eqPowLang (0 : Fin 3) 1).IsContextFree :=
  eqPowLang_isContextFree _ _

/-- A concrete word of `a^n b^n c^n`, in a language that is not
context-free. -/
theorem anbncn_example :
    ([0, 0, 1, 1, 2, 2] : List (Fin 3)) ∈ anbncnLang ∧
      ¬ anbncnLang.IsContextFree :=
  ⟨⟨2, by decide⟩, anbncnLang_not_isContextFree⟩

/-- The star of a singleton contains constant words. -/
theorem kstar_singleton_example :
    ([2, 2, 2] : List (Fin 3)) ∈
      KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)) :=
  mem_kstar_singleton.mpr ⟨3, by decide⟩

/-- Intersection nonclosure as a client-facing universal statement. -/
theorem intersection_not_closed :
    ¬ ∀ L M : Language (Fin 3), L.IsContextFree → M.IsContextFree →
      (L ⊓ M).IsContextFree :=
  not_forall_isContextFree_inf

/-- Complement nonclosure as a client-facing universal statement. -/
theorem complement_not_closed :
    ¬ ∀ L : Language (Fin 3), L.IsContextFree → (Lᶜ).IsContextFree :=
  not_forall_isContextFree_compl

end Cslib.Language.ContextFreeNonClosureTests
