/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

/-!
# Weak preservation by the original functorial cofibrant replacement

The actual natural trivial-fibration counit and original two-out-of-three
show the existing canonical cofibrant replacement preserves every weak
map. No cofibrancy of the original endpoints or replacement comparison
outcome is assumed, and no parallel replacement is introduced.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
    [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- The SAME canonical functorial cofibrant replacement sends every original weak map to a weak map.
-/
theorem cofibrantReplacement_map_weakEquivalence {X Y : C} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence ((cofibrantReplacement (C := C)).map f) := by
  let Q := cofibrantReplacement (C := C)
  let q := cofibrantReplacementCounit (C := C)
  let _ : WeakEquivalence (q.app X) := by infer_instance
  let _ : WeakEquivalence (q.app Y) := by infer_instance
  have h : WeakEquivalence (Q.map f ≫ q.app Y) := by
    rw [q.naturality f]
    change WeakEquivalence (q.app X ≫ f)
    infer_instance
  exact (weakEquivalence_postcomp_iff (Q.map f) (q.app Y)).mp h

end HomotopicalAlgebra
