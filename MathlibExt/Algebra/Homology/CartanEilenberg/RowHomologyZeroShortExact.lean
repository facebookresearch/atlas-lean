/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyZeroDifferential
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The degree-zero vertical-homology short exact sequence

Let P be a Cartan–Eilenberg resolution in an abelian category. The resolution-direction
differential preserves the homology coordinate of its zero-row homology and has the boundary
coordinate as quotient. Consequently the original-degree-zero vertical-homology complex belongs
to the short exact sequence 0 → PH₀.complex → verticalHomology(P.bicomplex,0) → PB₀.complex → 0.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The first biproduct coordinate defines a
chain map PH₀.complex → P.bicomplex.verticalHomologyComplex(0), indexed by resolution degree. -/
noncomputable def cartanEilenbergVerticalHomologyZeroι :
    (P.homologyResolution 0).complex ⟶
      P.bicomplex.verticalHomologyComplex 0 :=
  ChainComplex.ofHom
    (fun a => biprod.inl ≫ (P.rowHomologyZeroIso a).inv)
    (fun a => by
      apply (cancel_mono (P.rowHomologyZeroIso a).hom).1
      change ((biprod.inl ≫ (P.rowHomologyZeroIso (a + 1)).inv) ≫
          HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) 0) ≫
            (P.rowHomologyZeroIso a).hom =
        ((P.homologyResolution 0).complex.d (a + 1) a ≫
          (biprod.inl ≫ (P.rowHomologyZeroIso a).inv)) ≫
            (P.rowHomologyZeroIso a).hom
      simp only [Category.assoc]
      rw [P.rowHomologyZeroIso_naturality]
      rw [Iso.inv_hom_id_assoc]
      rw [P.biprod_inl_comp_rowHomologyZeroCoordinateMap]
      rw [Iso.inv_hom_id]
      simp)

@[simp]
theorem cartanEilenbergVerticalHomologyZeroι_f (a : ℕ) :
    (P.cartanEilenbergVerticalHomologyZeroι).f a =
      biprod.inl ≫ (P.rowHomologyZeroIso a).inv :=
  rfl

@[reassoc (attr := simp)]
theorem cartanEilenbergVerticalHomologyZeroι_f_comp_rowHomologyZeroIso_hom
    (a : ℕ) :
    (P.cartanEilenbergVerticalHomologyZeroι).f a ≫
        (P.rowHomologyZeroIso a).hom =
      biprod.inl := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The second biproduct coordinate defines a
chain map P.bicomplex.verticalHomologyComplex(0) → PB₀.complex. -/
noncomputable def cartanEilenbergVerticalHomologyZeroπ :
    P.bicomplex.verticalHomologyComplex 0 ⟶
      (P.boundaryResolution 0).complex :=
  ChainComplex.ofHom
    (fun a => (P.rowHomologyZeroIso a).hom ≫ biprod.snd)
    (fun a => by
      change ((P.rowHomologyZeroIso (a + 1)).hom ≫ biprod.snd) ≫
          (P.boundaryResolution 0).complex.d (a + 1) a =
        HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) 0 ≫
          ((P.rowHomologyZeroIso a).hom ≫ biprod.snd)
      simp only [Category.assoc]
      rw [P.rowHomologyZeroIso_naturality_assoc]
      rw [P.rowHomologyZeroCoordinateMap_comp_biprod_snd])

@[simp]
theorem cartanEilenbergVerticalHomologyZeroπ_f (a : ℕ) :
    (P.cartanEilenbergVerticalHomologyZeroπ).f a =
      (P.rowHomologyZeroIso a).hom ≫ biprod.snd :=
  rfl

@[reassoc (attr := simp)]
theorem rowHomologyZeroIso_inv_comp_cartanEilenbergVerticalHomologyZeroπ_f
    (a : ℕ) :
    (P.rowHomologyZeroIso a).inv ≫
        (P.cartanEilenbergVerticalHomologyZeroπ).f a =
      biprod.snd := by
  simp

@[reassoc (attr := simp)]
theorem cartanEilenbergVerticalHomologyZeroι_comp_π :
    P.cartanEilenbergVerticalHomologyZeroι ≫
        P.cartanEilenbergVerticalHomologyZeroπ = 0 := by
  apply HomologicalComplex.hom_ext
  intro a
  change (P.cartanEilenbergVerticalHomologyZeroι).f a ≫
      (P.cartanEilenbergVerticalHomologyZeroπ).f a = 0
  simp [Category.assoc]

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The homology-coordinate inclusion and
boundary-coordinate projection form PH₀.complex → verticalHomology(0) → PB₀.complex, with zero
composite. -/
noncomputable def cartanEilenbergVerticalHomologyZeroShortComplex :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    P.cartanEilenbergVerticalHomologyZeroι
    P.cartanEilenbergVerticalHomologyZeroπ
    P.cartanEilenbergVerticalHomologyZeroι_comp_π

@[simp]
theorem cartanEilenbergVerticalHomologyZeroShortComplex_X₁ :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).X₁ =
      (P.homologyResolution 0).complex :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologyZeroShortComplex_X₂ :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).X₂ =
      P.bicomplex.verticalHomologyComplex 0 :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologyZeroShortComplex_X₃ :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).X₃ =
      (P.boundaryResolution 0).complex :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologyZeroShortComplex_f :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).f =
      P.cartanEilenbergVerticalHomologyZeroι :=
  rfl

@[simp]
theorem cartanEilenbergVerticalHomologyZeroShortComplex_g :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).g =
      P.cartanEilenbergVerticalHomologyZeroπ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def
    cartanEilenbergVerticalHomologyZeroDegreewiseIso (a : ℕ) :
    ShortComplex.mk
        (biprod.inl :
          (P.homologyResolution 0).complex.X a ⟶
            (P.homologyResolution 0).complex.X a ⊞
              (P.boundaryResolution 0).complex.X a)
        (biprod.snd :
          (P.homologyResolution 0).complex.X a ⊞
              (P.boundaryResolution 0).complex.X a ⟶
            (P.boundaryResolution 0).complex.X a)
        (by simp) ≅
      P.cartanEilenbergVerticalHomologyZeroShortComplex.map
        (HomologicalComplex.eval C (ComplexShape.down ℕ) a) :=
  ShortComplex.isoMk (Iso.refl _)
    (P.rowHomologyZeroIso a).symm (Iso.refl _)
    (by
      change (𝟙 _) ≫
          (P.cartanEilenbergVerticalHomologyZeroι).f a =
        biprod.inl ≫ (P.rowHomologyZeroIso a).inv
      rw [Category.id_comp]
      exact P.cartanEilenbergVerticalHomologyZeroι_f a)
    (by
      change (P.rowHomologyZeroIso a).inv ≫
          (P.cartanEilenbergVerticalHomologyZeroπ).f a =
        biprod.snd ≫ 𝟙 _
      rw [Category.comp_id]
      exact
        P.rowHomologyZeroIso_inv_comp_cartanEilenbergVerticalHomologyZeroπ_f a)

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def
    cartanEilenbergVerticalHomologyZeroDegreewiseSplitting (a : ℕ) :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex.map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) a)).Splitting :=
  ShortComplex.Splitting.ofIso
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      ((P.homologyResolution 0).complex.X a)
      ((P.boundaryResolution 0).complex.X a))
    (cartanEilenbergVerticalHomologyZeroDegreewiseIso P a)

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The canonical sequence 0 → PH₀.complex →
P.bicomplex.verticalHomologyComplex(0) → PB₀.complex → 0 is short exact in the category of
nonnegative chain complexes. -/
theorem cartanEilenbergVerticalHomologyZeroShortExact :
    (P.cartanEilenbergVerticalHomologyZeroShortComplex).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun a =>
      (cartanEilenbergVerticalHomologyZeroDegreewiseSplitting P a).shortExact)

end HomologicalComplex.CartanEilenbergResolution

end
