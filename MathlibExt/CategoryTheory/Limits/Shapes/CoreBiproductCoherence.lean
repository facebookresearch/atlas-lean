/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductFunctor

/-!
# Zero coherence for core left-biproduct translation

Left biproduct translation by the chosen zero object is naturally isomorphic
to the identity functor on `Core C`.  At a core object `X`, the component is
the core isomorphism induced by

```text
  (0 ⊞ X.of) ≅ X.of.
```

Its forward map is `biprod.snd`.  Naturality is exactly the existing
projection formula `biprod.map_snd`; no multiplication, triangle, pentagon,
or action coherence is asserted here.  In particular, the two functors are
naturally isomorphic, not claimed to be definitionally equal.
-/

@[expose] public section

noncomputable section

open CategoryTheory ZeroObject

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Translation by the chosen zero object is naturally isomorphic to the
identity functor on the core. -/
noncomputable def coreLeftBiprodZeroIso :
    coreLeftBiprodFunctor (0 : C) ≅ 𝟭 (Core C) :=
  NatIso.ofComponents
    (fun X => Core.isoMk (isoZeroBiprod (isZero_zero C)).symm)
    (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 (0 : C)) g.iso.hom ≫ biprod.snd =
          biprod.snd ≫ g.iso.hom
      exact biprod.map_snd _ _)

/-- The forward component is the core morphism induced by the zero-biproduct
projection isomorphism. -/
@[simp]
theorem coreLeftBiprodZeroIso_hom_app (X : Core C) :
    (coreLeftBiprodZeroIso (C := C)).hom.app X =
      (Core.isoMk (isoZeroBiprod (isZero_zero C)).symm).hom :=
  rfl

/-- The underlying map of the forward component is `biprod.snd`. -/
@[simp]
theorem coreLeftBiprodZeroIso_hom_app_iso_hom (X : Core C) :
    ((coreLeftBiprodZeroIso (C := C)).hom.app X).iso.hom =
      (biprod.snd : (0 : C) ⊞ X.of ⟶ X.of) :=
  rfl

end CategoryTheory.Limits

end
