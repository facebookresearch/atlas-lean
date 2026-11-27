/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Map

/-!
# Milnor K-ring map laws

Functoriality of the Milnor K-ring construction `F ↦ MilnorKRing F`.

Given field homomorphisms, `unitsAddHom`, `tensorMapAlg` / `tensorMap`, and the induced
Milnor map `map` all preserve identities and composition, establishing the functorial
assignment at each stage of the construction.
-/

@[expose] public section

open TensorAlgebra
open scoped TensorAlgebra

namespace MilnorK
namespace MilnorKRing

variable {F K L : Type*} [Field F] [Field K] [Field L]

/-! ### Additive map on units -/

/-- `unitsAddHom f` acts on additive units by `Units.map f` on the underlying unit. -/
@[simp]
theorem unitsAddHom_apply (f : F →+* K) (u : Fˣ) :
    unitsAddHom f (Additive.ofMul u) =
      Additive.ofMul (Units.map f.toMonoidHom u) := rfl

/-- The additive map on `Additive Fˣ` induced by `RingHom.id` is the identity. -/
@[simp]
theorem unitsAddHom_id :
    unitsAddHom (RingHom.id F) = AddMonoidHom.id (Additive Fˣ) := rfl

/-- Functoriality of `unitsAddHom`: it sends a composite of field homomorphisms to the
composite of the induced maps on additive units. -/
theorem unitsAddHom_comp (f : F →+* K) (g : K →+* L) :
    unitsAddHom (g.comp f) = (unitsAddHom g).comp (unitsAddHom f) := rfl

/-! ### Tensor algebra map -/

/-- The ℤ-algebra endomorphism on `TensorRing F` induced by the identity is the identity. -/
@[simp]
theorem tensorMapAlg_id : tensorMapAlg (RingHom.id F) = AlgHom.id ℤ (TensorRing F) := by
  apply TensorAlgebra.hom_ext
  ext x
  simp [tensorMapAlg_ι, unitsAddHom_id]

/-- Functoriality of the ℤ-algebra map on tensor rings: it preserves composition of field
homomorphisms. -/
theorem tensorMapAlg_comp (f : F →+* K) (g : K →+* L) :
    tensorMapAlg (g.comp f) = (tensorMapAlg g).comp (tensorMapAlg f) := by
  apply TensorAlgebra.hom_ext
  ext x
  simp [tensorMapAlg_ι, unitsAddHom_comp]

/-- The ring endomorphism on `TensorRing F` induced by the identity is the identity. -/
@[simp]
theorem tensorMap_id :
    tensorMap (RingHom.id F) = RingHom.id (TensorRing F) := by
  simp [tensorMap, tensorMapAlg_id]

/-- Functoriality of the ring map on tensor rings: it preserves composition of field
homomorphisms. -/
theorem tensorMap_comp (f : F →+* K) (g : K →+* L) :
    tensorMap (g.comp f) = (tensorMap g).comp (tensorMap f) := by
  apply RingHom.ext
  intro x
  simp [tensorMap, tensorMapAlg_comp]

/-! ### Milnor K-ring map -/

/-- The Milnor K-ring map induced by the identity field homomorphism is the identity. -/
@[simp]
theorem map_id : map (RingHom.id F) = RingHom.id (MilnorKRing F) := by
  apply MilnorKRing.hom_ext
  ext x
  simp [map_mk, tensorMap_id]

/-- Functoriality of the Milnor K-ring map: `map` sends a composite of field
homomorphisms to the composite of the induced Milnor K-ring homomorphisms. -/
theorem map_comp (f : F →+* K) (g : K →+* L) :
    map (g.comp f) = (map g).comp (map f) := by
  apply MilnorKRing.hom_ext
  ext x
  simp [map_mk, tensorMap_comp]

end MilnorKRing
end MilnorK
