/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FourierMukai

/-!
# Derived internal Hom of module sheaves

Let `K` be an object of the derived category `D(X)` of module sheaves on a scheme `X` whose
derived tensor functor `K ⊗ᴸ -` (`FourierMukai.derivedTensor`, the total left derived functor
of the cochain tensor product) is a left adjoint. The derived internal Hom `RHom(K, N)` is
the value at `N` of its right adjoint.

## Main declarations

* `internalHom X K N`: the derived internal Hom `RHom(K, N)`.
* `internalHomEquiv`: maps `A ⟶ RHom(K, N)` correspond to maps `K ⊗ᴸ A ⟶ N`.
* `precomp a N`: the map `RHom(K', N) ⟶ RHom(K, N)` induced by `a : K ⟶ K'`, contravariantly
  functorial in `a` (`precomp_id`, `precomp_comp`).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedInternalHom

open CategoryTheory _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry.FourierMukai

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedTensors.{0}]

/-- The derived internal Hom `RHom(K, N)`: the right adjoint of `K ⊗ᴸ -`, evaluated at `N`. -/
abbrev internalHom (X : Scheme.{0}) (K N : D X) [((derivedTensor X).obj K).IsLeftAdjoint] : D X :=
  (Functor.rightAdjoint ((derivedTensor X).obj K)).obj N

/-- Maps into `RHom(K, N)` are maps out of `K ⊗ᴸ -`. -/
def internalHomEquiv (X : Scheme.{0}) (K A N : D X) [((derivedTensor X).obj K).IsLeftAdjoint] :
    (((derivedTensor X).obj K).obj A ⟶ N) ≃ (A ⟶ internalHom X K N) :=
  (Adjunction.ofIsLeftAdjoint ((derivedTensor X).obj K)).homEquiv A N

/-- Precomposition along `a : K ⟶ K'`: the transpose of the composite
`K ⊗ᴸ RHom(K', N) ⟶ K' ⊗ᴸ RHom(K', N) ⟶ N` of `a ⊗ᴸ 1` with the evaluation map. -/
def precomp {X : Scheme.{0}} {K K' : D X} (a : K ⟶ K') (N : D X)
    [((derivedTensor X).obj K).IsLeftAdjoint] [((derivedTensor X).obj K').IsLeftAdjoint] :
    internalHom X K' N ⟶ internalHom X K N :=
  internalHomEquiv X K _ N (((derivedTensor X).map a).app (internalHom X K' N) ≫
    (Adjunction.ofIsLeftAdjoint ((derivedTensor X).obj K')).counit.app N)

@[simp]
theorem precomp_id {X : Scheme.{0}} (K N : D X) [((derivedTensor X).obj K).IsLeftAdjoint] :
    precomp (𝟙 K) N = 𝟙 (internalHom X K N) := by
  simp only [precomp, internalHomEquiv, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Adjunction.homEquiv_unit]
  exact (Adjunction.ofIsLeftAdjoint ((derivedTensor X).obj K)).right_triangle_components N

theorem precomp_comp {X : Scheme.{0}} {K K' K'' : D X} (a : K ⟶ K') (b : K' ⟶ K'') (N : D X)
    [((derivedTensor X).obj K).IsLeftAdjoint] [((derivedTensor X).obj K').IsLeftAdjoint]
    [((derivedTensor X).obj K'').IsLeftAdjoint] :
    precomp (a ≫ b) N = precomp b N ≫ precomp a N := by
  simp only [precomp, internalHomEquiv]
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
    ((derivedTensor X).map a).naturality_assoc]
  congr 1
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

end MathlibExt.AlgebraicGeometry.DerivedInternalHom
