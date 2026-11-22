/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.DiscreteCoproduct
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Copower descent into pointed internal Hom

For an arbitrary indexing type, maps from its based discrete copower to
the internal Hom of pointed spaces correspond to families of pointed maps
between those spaces in the stated universes. The cofan universal property
defines `copowerHomMap`, and its generator formula and extensionality give
both inverses of `copowerHomEquiv`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace PointedCGWH

/-- Extend an actual arrow family through the original based point copower into native Hom. -/
def copowerHomMap (E : Type w) (X Y : PointedCGWH.{u, max v w})
    (f : E → (X ⟶ Y)) : basedDiscreteObj.{u, v, w} E ⟶ (ihom X).obj Y :=
  (basedDiscreteCofanIsColimit.{u, v, w} E).desc
    (Cofan.mk _ (fun e => eHomEquiv PointedCGWH.{u, max v w} (f e)))

/-- The full Hom descent keeps every original unit-shaped coefficient arrow. -/
theorem copowerHomMap_generator (E : Type w) (X Y : PointedCGWH.{u, max v w})
    (f : E → (X ⟶ Y)) (e : E) :
    basedDiscreteIncl.{u, v, w} E e ≫ copowerHomMap.{u, v, w} E X Y f =
      eHomEquiv PointedCGWH.{u, max v w} (f e) :=
  (basedDiscreteCofanIsColimit.{u, v, w} E).fac
    (Cofan.mk _ (fun e => eHomEquiv PointedCGWH.{u, max v w} (f e))) ⟨e⟩

/-- Maps into the native internal Hom are determined by the actual original arrow legs. -/
theorem copowerHomMap_hom_ext (E : Type w) (X Y : PointedCGWH.{u, max v w})
    {f g : basedDiscreteObj.{u, v, w} E ⟶ (ihom X).obj Y}
    (h : ∀ e, basedDiscreteIncl.{u, v, w} E e ≫ f =
      basedDiscreteIncl.{u, v, w} E e ≫ g) : f = g :=
  IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} E) (fun ⟨e⟩ => h e)

/-- The original component arrow family is the complete unit-shaped Hom descent data. -/
def copowerHomEquiv (E : Type w) (X Y : PointedCGWH.{u, max v w}) :
    (basedDiscreteObj.{u, v, w} E ⟶ (ihom X).obj Y) ≃
      (E → (X ⟶ Y)) where
  toFun a e := (eHomEquiv PointedCGWH.{u, max v w}).symm
    (basedDiscreteIncl.{u, v, w} E e ≫ a)
  invFun := copowerHomMap.{u, v, w} E X Y
  left_inv a := by
    apply copowerHomMap_hom_ext.{u, v, w} E X Y
    intro e
    rw [copowerHomMap_generator, Equiv.apply_symm_apply]
    rfl
  right_inv f := by
    funext e
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let D : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} E
    let H : PointedCGWH.{u, max v w} := (ihom X).obj Y
    let l : U ⟶ D := basedDiscreteIncl.{u, v, w} E e
    let m : D ⟶ H := copowerHomMap.{u, v, w} E X Y f
    let eh : (X ⟶ Y) ≃ (U ⟶ H) := eHomEquiv PointedCGWH.{u, max v w}
    have h : l ≫ m = eh (f e) := copowerHomMap_generator.{u, v, w} E X Y f e
    have hi : eh.symm (eh (f e)) = f e := eh.symm_apply_apply (f e)
    change eh.symm (l ≫ m) = f e
    exact (congrArg (fun t : U ⟶ H => eh.symm t) h).trans hi

end PointedCGWH
