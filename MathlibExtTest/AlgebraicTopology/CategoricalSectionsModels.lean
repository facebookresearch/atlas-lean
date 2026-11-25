/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory

/-!
# A noninvertible enhanced-category arrow consumer

The full enhanced subcategory keeps the actual arrow 0→1 of nerve(Fin2).
Its inverse-edge core excludes that arrow. This detects replacing an
enhanced full category by its Kan core when defining Perf descent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicTopology.CategoricalSectionsModels

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open scoped Simplicial

def category := nerve (Fin 2)

def forward : category _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

theorem full_keeps_forward :
    forward ∈ (category.fullEnhancedSubcategory (fun _ => True)).obj (op ⦋1⦌) := by
  apply (SSet.mem_fullEnhancedSubcategory_obj_iff (fun _ => True) forward).2
  intro v
  trivial

theorem forward_not_equivalence : ¬ IsEquivalenceEdge category forward := by
  rintro ⟨g, a, b, hae, hag, haa, hbg, hbe, hbb⟩
  have h1 : a.obj (1 : Fin 3) = 1 := by
    have h := congrArg (fun t : category _⦋1⦌ => t.obj (1 : Fin 2)) hae
    change a.obj (1 : Fin 3) = 1 at h
    exact h
  have h2 : a.obj (2 : Fin 3) = 0 := by
    have h := congrArg (fun t : category _⦋1⦌ => t.obj (1 : Fin 2)) haa
    change a.obj (2 : Fin 3) = 0 at h
    exact h
  have h := leOfHom (a.map (homOfLE (show (1 : Fin 3) ≤ 2 by decide)))
  rw [h1, h2] at h
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) h

end MathlibExtTest.AlgebraicTopology.CategoricalSectionsModels
