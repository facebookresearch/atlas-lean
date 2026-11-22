/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MonoFactorization

/-!
# Functoriality of the original marked mono factorization

The same original simplicial mono factorization is functorial on whole
arrow squares. Its actual intermediate map preserves the target-preimage
marking by the right-factor naturality equation. Both original left and
right triangles remain the corresponding marked triangles. This gives
native functorial factorization for the proved marked mono weak
factorization system, without a new general functor-model construction.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The intermediate marked object and original square map of the chosen native mono factorization. -/
def monoFactorizationFunctor : Arrow Marked.{u} ⥤ Marked.{u} where
  obj f := (monoFactorizationData f.hom).Z
  map {f g} φ := by
    let r := modelCategoryQuillen.monoFunctorialFactorizationData.{u}
    let ψ := forget.{u}.mapArrow.map φ
    refine ⟨r.Z.map ψ, fun {e} he => ?_⟩
    change (r.p.app (forget.mapArrow.obj g)).app (op ⦋1⦌)
      ((r.Z.map ψ).app (op ⦋1⦌) e) ∈ g.right.marking
    have h := ConcreteCategory.congr_hom (congr_app (r.p.naturality ψ) (op ⦋1⦌)) e
    exact h.symm ▸ φ.right.preserve he
  map_id f := by
    apply Hom.ext
    change modelCategoryQuillen.monoFunctorialFactorizationData.Z.map
      (forget.mapArrow.map (𝟙 f)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp φ ψ := by
    apply Hom.ext
    change modelCategoryQuillen.monoFunctorialFactorizationData.Z.map
      (forget.mapArrow.map (φ ≫ ψ)) =
      modelCategoryQuillen.monoFunctorialFactorizationData.Z.map (forget.mapArrow.map φ) ≫
      modelCategoryQuillen.monoFunctorialFactorizationData.Z.map (forget.mapArrow.map ψ)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- The whole actual left factor is natural in original marked arrow squares. -/
def monoFactorizationLeft : (Arrow.leftFunc : Arrow Marked.{u} ⥤ Marked.{u}) ⟶
    monoFactorizationFunctor where
  app f := (monoFactorizationData f.hom).i
  naturality {f g} φ := Hom.ext
    (modelCategoryQuillen.monoFunctorialFactorizationData.i.naturality (forget.mapArrow.map φ))

/-- The whole original right factor has its native marked naturality square. -/
def monoFactorizationRight : monoFactorizationFunctor.{u} ⟶ Arrow.rightFunc where
  app f := (monoFactorizationData f.hom).p
  naturality {f g} φ := Hom.ext
    (modelCategoryQuillen.monoFunctorialFactorizationData.p.naturality (forget.mapArrow.map φ))

/-- The native marked mono/right-lifting factorization is genuinely functorial on original arrows. -/
def monoFunctorialFactorizationData :
    FunctorialFactorizationData (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp where
  Z := monoFactorizationFunctor
  i := monoFactorizationLeft
  p := monoFactorizationRight
  fac := by
    apply NatTrans.ext
    funext f
    change (monoFactorizationData f.hom).i ≫ (monoFactorizationData f.hom).p = f.hom
    exact (monoFactorizationData f.hom).fac
  hi f := by
    change Mono (monoFactorizationData f.hom).i
    exact (monoFactorizationData f.hom).hi
  hp f := by
    change (monomorphisms Marked.{u}).rlp (monoFactorizationData f.hom).p
    exact (monoFactorizationData f.hom).hp

/-- Each original square map is exactly the original simplicial mono-factorization square map. -/
@[simp]
theorem monoFactorizationFunctor_map_hom {f g : Arrow Marked.{u}} (φ : f ⟶ g) :
    (monoFactorizationFunctor.map φ).hom =
      modelCategoryQuillen.monoFunctorialFactorizationData.Z.map (forget.mapArrow.map φ) := rfl

/-- The actual original value-universe factorization admits the native functorial-factorization class. -/
theorem mono_hasFunctorialFactorization :
    HasFunctorialFactorization (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp :=
  ⟨⟨monoFunctorialFactorizationData⟩⟩

end SSet.Marked
