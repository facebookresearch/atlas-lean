/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Products

/-!
# Selected points of native CGWH products

The existing bijective carrier comparison specifies a native product point
with prescribed coordinates. This uses only an equivalence of carriers;
no ordinary-product homeomorphism or H-space structure is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CGWH

/-- The pointwise equivalence from the native CGWH product carrier to the
ordinary pair.  It is deliberately only an `Equiv`, not a homeomorphism. -/
@[expose] public noncomputable def prodPointEquiv (X Y : CGWH.{u, v}) :
    (X ⨯ Y : CGWH.{u, v}) ≃ (X × Y) :=
  Equiv.ofBijective (prodComparisonToTop X Y)
    (prodComparisonToTop_bijective X Y)

/-- The native-product point with prescribed two coordinates. -/
@[expose] public noncomputable def prodPoint (X Y : CGWH.{u, v}) (x : X) (y : Y) :
    (X ⨯ Y : CGWH.{u, v}) :=
  (prodPointEquiv X Y).symm (x, y)

@[simp]
public theorem prodPointEquiv_apply (X Y : CGWH.{u, v})
    (z : (X ⨯ Y : CGWH.{u, v})) :
    prodPointEquiv X Y z = prodComparisonToTop X Y z :=
  rfl

@[simp]
public theorem prodComparisonToTop_prodPoint (X Y : CGWH.{u, v})
    (x : X) (y : Y) :
    @DFunLike.coe
      (ContinuousMap
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj (X ⨯ Y : CGWH.{u, v})))
        ((CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj X)) ×
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj Y))))
      (CompactlyGenerated.compactlyGeneratedToTop.obj
        (CGWH.cgwhToCompactlyGenerated.obj (X ⨯ Y : CGWH.{u, v})))
      (fun _ =>
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj X)) ×
        (CompactlyGenerated.compactlyGeneratedToTop.obj
          (CGWH.cgwhToCompactlyGenerated.obj Y)))
      _ (ConcreteCategory.hom (prodComparisonToTop X Y))
      (prodPoint X Y x y) = (x, y) :=
  (prodPointEquiv X Y).apply_symm_apply (x, y)

@[simp]
public theorem prodPoint_fst (X Y : CGWH.{u, v}) (x : X) (y : Y) :
    (Limits.prod.fst : X ⨯ Y ⟶ X) (prodPoint X Y x y) = x := by
  have h := ConcreteCategory.congr_hom
    (prodComparisonToTop_fst X Y) (prodPoint X Y x y)
  change (prodComparisonToTop X Y (prodPoint X Y x y)).1 =
    (Limits.prod.fst : X ⨯ Y ⟶ X) (prodPoint X Y x y) at h
  rw [prodComparisonToTop_prodPoint] at h
  exact h.symm

@[simp]
public theorem prodPoint_snd (X Y : CGWH.{u, v}) (x : X) (y : Y) :
    (Limits.prod.snd : X ⨯ Y ⟶ Y) (prodPoint X Y x y) = y := by
  have h := ConcreteCategory.congr_hom
    (prodComparisonToTop_snd X Y) (prodPoint X Y x y)
  change (prodComparisonToTop X Y (prodPoint X Y x y)).2 =
    (Limits.prod.snd : X ⨯ Y ⟶ Y) (prodPoint X Y x y) at h
  rw [prodComparisonToTop_prodPoint] at h
  exact h.symm

/-- Evaluation of a categorical product lift in native-product
coordinates. -/
@[simp]
public theorem prod_lift_apply {Z X Y : CGWH.{u, v}}
    (f : Z ⟶ X) (g : Z ⟶ Y) (z : Z) :
    Limits.prod.lift f g z = prodPoint X Y (f z) (g z) := by
  apply (prodComparisonToTop_bijective X Y).1
  rw [prodComparisonToTop_prodPoint]
  apply Prod.ext
  · have h₁ := ConcreteCategory.congr_hom
      (prodComparisonToTop_fst X Y) (Limits.prod.lift f g z)
    have h₂ := ConcreteCategory.congr_hom (Limits.prod.lift_fst f g) z
    change (prodComparisonToTop X Y (Limits.prod.lift f g z)).1 =
      (Limits.prod.fst : X ⨯ Y ⟶ X) (Limits.prod.lift f g z) at h₁
    change (Limits.prod.fst : X ⨯ Y ⟶ X)
      (Limits.prod.lift f g z) = f z at h₂
    exact h₁.trans h₂
  · have h₁ := ConcreteCategory.congr_hom
      (prodComparisonToTop_snd X Y) (Limits.prod.lift f g z)
    have h₂ := ConcreteCategory.congr_hom (Limits.prod.lift_snd f g) z
    change (prodComparisonToTop X Y (Limits.prod.lift f g z)).2 =
      (Limits.prod.snd : X ⨯ Y ⟶ Y) (Limits.prod.lift f g z) at h₁
    change (Limits.prod.snd : X ⨯ Y ⟶ Y)
      (Limits.prod.lift f g z) = g z at h₂
    exact h₁.trans h₂

end CGWH

end
