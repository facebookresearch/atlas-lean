/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Category/ModuleCat/Monoidal/Forget.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The lax monoidal forgetful functor on modules

The forgetful functor from modules to types sends a pair of elements to their pure tensor,
and the unique element of the cartesian unit to `1`. Its lax monoidal structure lets one
pass from enrichment in simplicial modules to enrichment in simplicial sets.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.DGSource

universe u

variable (R : Type u) [CommRing R]

/-- Forgetting modules is lax monoidal: the tensor comparison is the pure tensor map. -/
noncomputable instance moduleCatForgetLaxMonoidal : (forget (ModuleCat.{u} R)).LaxMonoidal :=
  (ModuleCat.adj R).rightAdjointLaxMonoidal

/-- The lax unit of the module forgetful functor selects `1`. -/
@[simp]
lemma moduleCatForget_ε_apply (x : 𝟙_ (Type u)) :
    dsimp% Functor.LaxMonoidal.ε (forget (ModuleCat.{u} R)) x = (1 : R) := by
  cases x
  simp [Adjunction.rightAdjointLaxMonoidal_ε,
    ModuleCat.adj_homEquiv, ModuleCat.freeHomEquiv]

/-- The tensor comparison of the module forgetful functor forms a pure tensor. -/
@[simp]
lemma moduleCatForget_μ_apply (M N : ModuleCat.{u} R) (x : M) (y : N) :
    dsimp% Functor.LaxMonoidal.μ (forget (ModuleCat.{u} R)) M N (x, y) = x ⊗ₜ[R] y := by
  simp [Adjunction.rightAdjointLaxMonoidal_μ, ← (ModuleCat.adj R).homEquiv_symm_id,
    ModuleCat.adj_homEquiv, ModuleCat.freeHomEquiv]

end MathlibExt.DGSource
