/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Preadditive.HomIso
public import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Full represented Hom functions and exactness through source isomorphisms

The actual native Hom correspondence is additive, with both complete
composition functions. A whole source ladder transports exactness by
Mathlib's additive-equivalence ladder theorem. Applied to a native
triangle Iso, all three represented row positions keep every component
and the actual shifted component maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Pretriangulated

namespace CategoryTheory.Preadditive.HomIsoExact

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasShift C ℤ]

/-- A whole native triangle Iso transports its full input/inclusion Hom exactness. -/
theorem triangle_input_iso {T T' : Triangle C} (a : T ≅ T') (E : C) :
    Function.Exact (Preadditive.leftComp E T'.mor₂) (Preadditive.leftComp E T'.mor₁) ↔
      Function.Exact (Preadditive.leftComp E T.mor₂) (Preadditive.leftComp E T.mor₁) :=
  represented_source_iso T.mor₁ T.mor₂ T'.mor₁ T'.mor₂
    ((Triangle.π₁).mapIso a) ((Triangle.π₂).mapIso a) ((Triangle.π₃).mapIso a)
    a.hom.comm₁ a.hom.comm₂ E

/-- All three original triangle components transport the entire inclusion/boundary Hom row. -/
theorem triangle_boundary_iso {T T' : Triangle C} (a : T ≅ T') (E : C) :
    Function.Exact (Preadditive.leftComp E T'.mor₃) (Preadditive.leftComp E T'.mor₂) ↔
      Function.Exact (Preadditive.leftComp E T.mor₃) (Preadditive.leftComp E T.mor₂) :=
  represented_source_iso T.mor₂ T.mor₃ T'.mor₂ T'.mor₃
    ((Triangle.π₂).mapIso a) ((Triangle.π₃).mapIso a)
    ((shiftFunctor C 1).mapIso ((Triangle.π₁).mapIso a))
    a.hom.comm₂ a.hom.comm₃ E

/-- The actual shifted component square transports the preceding suspended-input/boundary position. -/
theorem triangle_suspension_iso {T T' : Triangle C} (a : T ≅ T') (E : C) :
    Function.Exact (Preadditive.leftComp E ((shiftFunctor C 1).map T'.mor₁))
        (Preadditive.leftComp E T'.mor₃) ↔
      Function.Exact (Preadditive.leftComp E ((shiftFunctor C 1).map T.mor₁))
        (Preadditive.leftComp E T.mor₃) := by
  apply represented_source_iso T.mor₃ ((shiftFunctor C 1).map T.mor₁)
    T'.mor₃ ((shiftFunctor C 1).map T'.mor₁) ((Triangle.π₃).mapIso a)
    ((shiftFunctor C 1).mapIso ((Triangle.π₁).mapIso a))
    ((shiftFunctor C 1).mapIso ((Triangle.π₂).mapIso a)) a.hom.comm₃
  change (shiftFunctor C 1).map T.mor₁ ≫ (shiftFunctor C 1).map a.hom.hom₂ =
    (shiftFunctor C 1).map a.hom.hom₁ ≫ (shiftFunctor C 1).map T'.mor₁
  simpa only [Functor.map_comp] using (shiftFunctor C 1).congr_map a.hom.comm₁

end CategoryTheory.Preadditive.HomIsoExact
