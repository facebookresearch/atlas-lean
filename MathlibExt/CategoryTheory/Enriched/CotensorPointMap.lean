/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.CotensorOrdinaryComparison

/-!
# Unit-point maps on enriched cotensors

For a monoidal closed category and an enriched index, a unit point of an
index Hom object induces a map on the cotensor of an enriched functor.
This map is the internal-Hom target map of the corresponding ordinary
morphism. No ordinary category structure on the enriched index is needed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor.CotensorPointMap
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

/-- An original unit point of any enriched index acts on the actual cotensor by the original
internal-Hom target map. This requires no ordinary category structure on the enriched index. -/
theorem map (M : V) (G : EnrichedFunctor V I V) (a b : I)
    (p : (𝟙_ V) ⟶ (a ⟶[V] b)) :
    (eHomEquiv V).symm (p ≫ (EnrichedFunctor.cotensor M G).map a b) =
      (ihom M).map ((eHomEquiv V).symm (p ≫ G.map a b)) := by
  let X := G.obj a
  let Y := G.obj b
  let R := EnrichedFunctor.covariantRepresentable V V M
  let g : X ⟶ Y := (eHomEquiv V).symm (p ≫ G.map a b)
  let f : (ihom M).obj X ⟶ (ihom M).obj Y :=
    (eHomEquiv V).symm (p ≫ (EnrichedFunctor.cotensor M G).map a b)
  have hg : eHomEquiv V g = p ≫ G.map a b := (eHomEquiv V).apply_symm_apply _
  have hf : eHomEquiv V f = p ≫ (G.map a b ≫ R.map X Y) :=
    (eHomEquiv V).apply_symm_apply _
  have hr : eHomEquiv V ((ihom M).map g) = eHomEquiv V g ≫ R.map X Y := by
    have h := EnrichedFunctor.toOrdinaryFunctor_map R g
    have hm := CotensorOrdinaryComparison.representable_map M g
    exact (congrArg (fun t : (ihom M).obj X ⟶ (ihom M).obj Y => eHomEquiv V t) hm).symm.trans h
  change f = (ihom M).map g
  apply (eHomEquiv V).injective
  exact hf.trans ((Category.assoc p (G.map a b) (R.map X Y)).symm.trans
    ((congrArg (fun t => t ≫ R.map X Y) hg.symm).trans hr.symm))

end CategoryTheory.EnrichedFunctor.CotensorPointMap
